//===--- UnnecessaryCopyOnLastUseCheck.cpp - clang-tidy -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "UnnecessaryCopyOnLastUseCheck.h"
#include "../utils/Matchers.h"
#include "../utils/OptionsUtils.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/LambdaCapture.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/Lambda.h"
#include "clang/Basic/LangStandard.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Lexer.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/FormatVariadic.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <iterator>
#include <sstream>
#include <type_traits>
#include <utility>

using namespace clang;
using namespace clang::tidy;
using namespace clang::tidy::performance;
using namespace clang::ast_matchers;

static constexpr auto BlockedTypesOption = "BlockedTypes";
static constexpr auto BlockedFunctionsOption = "BlockedFunctions";

namespace {
struct FindDeclRefBlockReturn {
  const CFGBlock *DeclRefBlock = nullptr;
  CFGBlock::const_iterator StartElement{};
};

enum class Usage {
  Error = -1,
  Usage = 0,
  DefiniteLastUse,
  LikelyDefiniteLastUse,
};

} // namespace

static FindDeclRefBlockReturn findDeclRefBlock(CFG const *TheCFG,
                                               const DeclRefExpr *DeclRef) {
  for (CFGBlock *Block : *TheCFG) {
    auto Iter =
        llvm::find_if(Block->Elements, [&, DeclRef](const CFGElement &Element) {
          if (Element.getKind() == CFGElement::Statement) {
            return Element.template castAs<CFGStmt>().getStmt() == DeclRef;
          }
          return false;
        });
    if (Iter != Block->Elements.end()) {
      return {Block, ++Iter};
    }
  }
  return {nullptr, {}};
}

static const clang::CFGElement *
nextUsageInCurrentBlock(const FindDeclRefBlockReturn &StartBlockElement,
                        const DeclRefExpr *DeclRef) {
  // Search for uses in the current block
  auto Begi = StartBlockElement.StartElement;
  auto Endi = StartBlockElement.DeclRefBlock->Elements.end();
  auto Iter = std::find_if(Begi, Endi, [&](const CFGElement &Element) {
    if (Element.getKind() == CFGElement::Statement) {
      if (auto *Stmt = Element.template castAs<CFGStmt>().getStmt()) {
        if (auto *DRE = dyn_cast<DeclRefExpr>(Stmt)) {
          if (DRE->getDecl() == DeclRef->getDecl()) {
            return true;
          }
        }
      }
    }
    return false;
  });
  return Iter != Endi ? &*Iter : nullptr;
}

static bool isLHSOfAssignment(const DeclRefExpr *DeclRef, ASTContext &Context) {
  const TraversalKindScope RAII(Context, TK_IgnoreUnlessSpelledInSource);
  // Todo (performance): While this is faster than a match expression,
  //      it would be faster to start from the DeclRefExpr directly
  struct IsLHSOfAssignment : RecursiveASTVisitor<IsLHSOfAssignment> {
    const DeclRefExpr *Ref{};

    IsLHSOfAssignment(const DeclRefExpr *Ref, ASTContext &Context) : Ref(Ref) {}

    bool shouldWalkTypesOfTypeLocs() const { return false; }
    bool shouldVisitTemplateInstantiations() const { return true; }

    bool VisitCXXOperatorCallExpr(CXXOperatorCallExpr *BO) {
      if (BO->isAssignmentOp()) {
        if (auto *DRE =
                dyn_cast<DeclRefExpr>(BO->getArg(0)->IgnoreParenImpCasts())) {
          if (DRE && DRE == Ref) {
            return false;
          }
        }
      }
      return true;
    }
  };
  return !IsLHSOfAssignment{DeclRef, Context}.TraverseAST(Context);
}

// Todo (improvement): Expand this Visitor to also determine, if an explicit
// CaptureInitExpr is used or if a DeclRefExpr is used implicitelly via a
// cature default
struct DeclRefInLambdaCaptureMatcher
    : RecursiveASTVisitor<DeclRefInLambdaCaptureMatcher> {
  const DeclRefExpr *Ref{};
  // Ret:
  struct Return {
    LambdaExpr const *Lambda{};
    LambdaCapture const *Capture{};
  } Ret;

  DeclRefInLambdaCaptureMatcher(const DeclRefExpr *Ref) : Ref(Ref) {}

  bool shouldWalkTypesOfTypeLocs() const { return false; }
  bool shouldVisitTemplateInstantiations() const { return true; }

  bool VisitLambdaExpr(LambdaExpr *Lambda) {

    for (auto &&[/* Expr * */ Init,
                 /* const LambdaCapture & */ Capture] :
         llvm::zip(Lambda->capture_inits(), Lambda->captures())) {
      auto *S = cast<Stmt>(Init);
      llvm::SmallVector<Stmt *, 6> Childs;
      while (S != nullptr) {
        if (auto *DeclRef = dyn_cast<DeclRefExpr>(S);
            DeclRef != nullptr && Ref == DeclRef) {
          this->Ret.Lambda = Lambda;
          this->Ret.Capture = &Capture;
          return false;
        }
        Childs.append(S->child_begin(), S->child_end());
        S = Childs.empty() ? nullptr : Childs.pop_back_val();
      }
    }
    return true;
  }
};

static DeclRefInLambdaCaptureMatcher::Return
isInLambdaCapture(const DeclRefExpr *MyDeclRef, ASTContext &Context) {
  auto Matcher = DeclRefInLambdaCaptureMatcher{MyDeclRef};
  Matcher.TraverseAST(Context);
  return Matcher.Ret;
}

static Usage definiteLastUse(ASTContext *Context, CFG *const TheCFG,
                             const DeclRefExpr *DeclRef) {
  if (TheCFG == nullptr) {
    return Usage::Error;
  }

  // Find the CFGBlock containing the DeclRefExpr
  auto StartBlockElement = findDeclRefBlock(TheCFG, DeclRef);
  if (StartBlockElement.DeclRefBlock == nullptr) {
    return Usage::Error; // Todo(unexpected): DeclRefExpr not found in CFG
  }

  // Find next uses of the DeclRefExpr

  auto TraverseCFGForUsage = [&]() -> Usage {
    llvm::SmallPtrSet<CFGBlock const *, 8> VisitedBlocks;
    llvm::SmallVector<CFGBlock const *, 8> Worklist;

    auto HandleInternal = [&](FindDeclRefBlockReturn const &BlockElement) {
      CFGElement const *NextUsageE =
          nextUsageInCurrentBlock(BlockElement, DeclRef);
      if (NextUsageE) {
        if (bool const IsLastUsage =
                isLHSOfAssignment(llvm::cast<DeclRefExpr>(
                                      NextUsageE->castAs<CFGStmt>().getStmt()),
                                  *Context);
            !IsLastUsage) {
          return Usage::Usage;
        }
        return Usage::DefiniteLastUse;
      }
      assert(BlockElement.DeclRefBlock);
      // No successing DeclRefExpr found, appending successors
      for (CFGBlock const *Succ : BlockElement.DeclRefBlock->succs()) {
        if (Succ) { // Succ can be nullptr, if a block is unreachable
          Worklist.push_back(Succ);
        }
      }
      return Usage::DefiniteLastUse; // No usage found, assume last use
    };

    if (auto FoundUsage = HandleInternal(StartBlockElement);
        FoundUsage == Usage::Usage) { // Usage found
      return FoundUsage;
    }
    while (!Worklist.empty()) {
      CFGBlock const *Block = Worklist.pop_back_val();
      if (!VisitedBlocks.insert(Block).second) {
        continue;
      }
      if (auto FoundUsage = HandleInternal({Block, Block->Elements.begin()});
          FoundUsage == Usage::Usage) {
        return FoundUsage;
      }
    }
    return Usage::DefiniteLastUse;
  };

  return TraverseCFGForUsage();
}

namespace clang::tidy::performance {

UnnecessaryCopyOnLastUseCheck::~UnnecessaryCopyOnLastUseCheck() = default;

UnnecessaryCopyOnLastUseCheck::UnnecessaryCopyOnLastUseCheck(
    StringRef Name, ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context),
      Inserter(Options.getLocalOrGlobal("IncludeStyle",
                                        utils::IncludeSorter::IS_LLVM),
               areDiagsSelfContained()),
      BlockedTypes(
          utils::options::parseStringList(Options.get(BlockedTypesOption, ""))),
      BlockedFunctions(utils::options::parseStringList(
          Options.get(BlockedFunctionsOption, ""))),
      CFGs() {}

void UnnecessaryCopyOnLastUseCheck::registerMatchers(MatchFinder *Finder) {
  const auto ValueParameter =
      declRefExpr(
          to(valueDecl(
              unless(varDecl(unless(hasAutomaticStorageDuration()))),
              hasType(qualType(
                  hasCanonicalType(qualType(
                      matchers::isExpensiveToCopy(),
                      unless(anyOf(isConstQualified(), lValueReferenceType(),
                                   pointerType())))),
                  unless(hasDeclaration(namedDecl(
                      matchers::matchesAnyListedName(BlockedTypes))) //
                         ))))))
          .bind("param");

  const auto IsMoveAssignable = cxxOperatorCallExpr(
      hasDeclaration(cxxMethodDecl(
          isCopyAssignmentOperator(),
          ofClass(hasMethod(cxxMethodDecl(isMoveAssignmentOperator(),
                                          unless(isDeleted())))))),
      hasRHS(ValueParameter));

  const auto IsMoveConstructible =
      ignoringElidableConstructorCall(ignoringParenImpCasts(
          cxxConstructExpr(
              unless(hasParent(callExpr(hasDeclaration(namedDecl(
                  matchers::matchesAnyListedName(BlockedFunctions)))))),
              hasDeclaration(cxxConstructorDecl(
                  isCopyConstructor(),
                  ofClass(hasMethod(cxxConstructorDecl(isMoveConstructor(),
                                                       unless(isDeleted())))))),
              hasArgument(0, ValueParameter))
              .bind("constructExpr")));

  Finder->addMatcher(stmt(anyOf(IsMoveAssignable, expr(IsMoveConstructible))),
                     this);
}

void UnnecessaryCopyOnLastUseCheck::check(
    const MatchFinder::MatchResult &Result) {
  const auto *Param = Result.Nodes.getNodeAs<DeclRefExpr>("param");
  const ValueDecl *const DeclOfParam = Param->getDecl();
  const DeclContext *const FunctionOfDeclContext =
      DeclOfParam->getParentFunctionOrMethod();

  if (!FunctionOfDeclContext) {
    // The parameter is not defined in a function, therefore it is not
    // possible to check if it is the last use via CFG analysis
    // Todo (improvement): Add a flag to show unanalyzable cases
    return;
  }

  const auto *const FunctionOfDecl =
      llvm::cast<FunctionDecl>(FunctionOfDeclContext);

  const auto *const VarDeclVal = llvm::dyn_cast<VarDecl>(DeclOfParam);
  if (!VarDeclVal) {
    return;
  }

  Usage DefiniteLastUse = definiteLastUse(
      Result.Context, getOrCreateCFG(FunctionOfDecl, Result.Context), Param);

  if (DefiniteLastUse == Usage::Usage || DefiniteLastUse == Usage::Error) {
    return;
  }

  // Template code cant be fixed currently
  if (!FunctionOfDecl->isTemplateInstantiation()) {

    if (DeclRefInLambdaCaptureMatcher::Return Ret =
            isInLambdaCapture(Param, *Result.Context);
        Ret.Lambda != nullptr && Ret.Capture != nullptr) {
      this->emplaceLambdaCapture(Ret.Lambda, Ret.Capture);
      return;
    }

    clang::SourceManager &SM = *Result.SourceManager;

    auto Diag =
        diag(Param->getExprLoc(),
             "Value '%0' is copied on last use, consider moving it instead.")
        << Param->getDecl()->getNameAsString();

    if (auto *CExpr = Result.Nodes.getNodeAs<CXXConstructExpr>("constructExpr");
        (CExpr && CExpr->getExprLoc().isMacroID())) {
      return;
    }

    auto MVStmt = "std::move(" + Param->getDecl()->getNameAsString() + ")";
    Diag << FixItHint::CreateReplacement(Param->getSourceRange(), MVStmt)
         << Param->getDecl()->getNameAsString()
         << Inserter.createIncludeInsertion(SM.getFileID(Param->getBeginLoc()),
                                            "<utility>");
  } else { // Template code can't be fixed currently, also a std::forward may be
           // more appropriate
    auto Diag =
        diag(Param->getExprLoc(), "Value '%0' may be copied on last use, "
                                  "consider forwarding it instead.")
        << Param->getDecl()->getNameAsString();
  }
}

void UnnecessaryCopyOnLastUseCheck::registerPPCallbacks(
    const SourceManager &SM, Preprocessor *PP, Preprocessor *ModuleExpanderPP) {
  Inserter.registerPreprocessor(PP);
  this->SMP = &SM;
}

void UnnecessaryCopyOnLastUseCheck::storeOptions(
    ClangTidyOptions::OptionMap &Opts) {
  Options.store(Opts, "IncludeStyle", Inserter.getStyle());
  Options.store(Opts, BlockedTypesOption,
                utils::options::serializeStringList(BlockedTypes));
  Options.store(Opts, BlockedFunctionsOption,
                utils::options::serializeStringList(BlockedFunctions));
}

void UnnecessaryCopyOnLastUseCheck::onEndOfTranslationUnit() {
  assert(this->getLangOpts().CPlusPlus);
  this->generateLambdaCaptureDiagnostics(*this, Inserter, *SMP,
                                         (!this->getLangOpts().CPlusPlus11));
}

static CFG::BuildOptions createBuildOptions() {
  CFG::BuildOptions Options;
  Options.setAlwaysAdd(DeclRefExpr::DeclRefExprClass);
  Options.AddImplicitDtors = true;
  Options.AddTemporaryDtors = true;
  return Options;
}

CFG *UnnecessaryCopyOnLastUseCheck::getOrCreateCFG(const FunctionDecl *FD,
                                                   ASTContext *C) {
  static auto BO = createBuildOptions();
  if (auto Iter = this->CFGs.find(FD); Iter != this->CFGs.end()) {
    return Iter->second.get();
  }

  auto EmplaceResult =
      this->CFGs.try_emplace(FD, CFG::buildCFG(nullptr, FD->getBody(), C, BO));
  return EmplaceResult.first->second.get();
}

UnnecessaryCopyOnLastUseCheck::LambdaCaptureMap::const_iterator
endOf(UnnecessaryCopyOnLastUseCheck::LambdaCaptureMap::const_iterator Begin,
      UnnecessaryCopyOnLastUseCheck::LambdaCaptureMap::const_iterator End) {
  return std::upper_bound(
      Begin, End, Begin->first,
      [](auto const &Value, auto const &Elem) { return Value < Elem.first; });
}

struct LambdaRangeIterator {
  using LambdaCaptureMap = UnnecessaryCopyOnLastUseCheck::LambdaCaptureMap;
  // ===
  using value_type = llvm::iterator_range<LambdaCaptureMap::const_iterator>;
  using difference_type = LambdaCaptureMap::const_iterator::difference_type;
  using reference = value_type;
  using pointer = value_type;
  using iterator_category = std::input_iterator_tag;
  // ===
  llvm::iterator_range<LambdaCaptureMap::const_iterator> Captures;
  LambdaCaptureMap const *Map;

  LambdaRangeIterator &operator++() {
    Captures = {Captures.end(), endOf(Captures.end(), Map->end())};
    return *this;
  }

  value_type &operator*() { return Captures; }

  friend bool operator==(LambdaRangeIterator const &Lhs,
                         LambdaRangeIterator const &Rhs) {
    return Lhs.Captures.begin() == Rhs.Captures.begin() &&
           Lhs.Captures.end() == Rhs.Captures.end();
  }

  friend bool operator!=(LambdaRangeIterator const &Lhs,
                         LambdaRangeIterator const &Rhs) {
    return !(Lhs == Rhs);
  }
};

static_assert(std::is_swappable_v<LambdaRangeIterator>);

void UnnecessaryCopyOnLastUseCheck::generateLambdaCaptureDiagnostics(
    ClangTidyCheck &CTC, utils::IncludeInserter &II, SourceManager const &SM,
    bool IsCXX14OrLater) {

  auto GetAllLambdas = [this]() -> llvm::iterator_range<LambdaRangeIterator> {
    return {
        LambdaRangeIterator{
            {this->CaptureList.begin(),
             endOf(this->CaptureList.begin(), this->CaptureList.end())},
            &this->CaptureList},
        LambdaRangeIterator{{this->CaptureList.end(), this->CaptureList.end()},
                            &this->CaptureList}};
  };

  for (auto &&LambdaCaptures : GetAllLambdas()) {
    LambdaExpr const *LExpr = LambdaCaptures.begin()->first;
    LambdaCaptureDefault Default = LExpr->getCaptureDefault();

    auto CapAndInits = llvm::zip(LExpr->captures(), LExpr->capture_inits());

    auto UntouchedCaptures =
        llvm::make_filter_range(CapAndInits, [&](const auto &I) {
          LambdaCapture const &Capture = std::get<0>(I);
          return Capture.isExplicit() &&
                 LambdaCaptures.end() !=
                     llvm::find_if(LambdaCaptures,
                                   [&](LambdaCaptureMapEntry const &Pair) {
                                     return &Capture == Pair.second;
                                   });
        });

    llvm::SmallVector<std::string, 4> CapturesAsStrings;
    if (Default != LCD_None) {
      CapturesAsStrings.emplace_back(Default == LCD_ByCopy ? "=" : "&");
    }

    for (auto &&I : UntouchedCaptures) {
      LambdaCapture const &Capture = std::get<0>(I);
      Expr const *Init = std::get<1>(I);
      CharSourceRange::getCharRange({Capture.getLocation(), Init->getEndLoc()});
      Lexer::getSourceText(CharSourceRange::getTokenRange(
                               {Capture.getLocation(), Init->getEndLoc()}),
                           SM, this->getLangOpts());
    }

    llvm::SmallVector<std::string, 4> CaptureParameterNames;
    for (auto &&CapturePair : LambdaCaptures) {
      auto Name = CapturePair.second->getCapturedVar()->getName();
      std::string CaptureString =
          llvm::formatv("{0} = std::move({0})", Name).str();
      CapturesAsStrings.emplace_back(CaptureString);
    }

    auto Diag =
        CTC.diag(LExpr->getIntroducerRange().getBegin(),
                 "Lambda captures '%0' are copied on last use, consider "
                 "moving them instead.")
        << llvm::join(CaptureParameterNames, ", ");

    if (IsCXX14OrLater) {
      return; // CXX11 does not support init captures
    }

    std::stringstream SStream{""};
    SStream << "[" << llvm::join(CapturesAsStrings, ", ") << "]";
    Diag << FixItHint::CreateReplacement(LExpr->getIntroducerRange(),
                                         SStream.str())
         << II.createIncludeInsertion(
                SM.getFileID(LExpr->getIntroducerRange().getBegin()),
                "<utility>");
  }
}

void UnnecessaryCopyOnLastUseCheck::emplaceLambdaCapture(
    LambdaExpr const *Lambda, LambdaCapture const *Capture) {
  // this->CaptureList must be sorted
  auto InsertPos = llvm::upper_bound(this->CaptureList,
                                     LambdaCaptureMapEntry{Lambda, Capture});
  this->CaptureList.emplace(InsertPos, Lambda, Capture);
  assert(llvm::is_sorted(this->CaptureList));
}

} // namespace clang::tidy::performance
