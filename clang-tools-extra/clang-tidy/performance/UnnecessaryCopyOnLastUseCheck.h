//===--- UnnecessaryCopyOnLastUseCheck.h - clang-tidy ------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_PERFORMANCE_UNNECESSARY_COPY_ON_LAST_USE_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_PERFORMANCE_UNNECESSARY_COPY_ON_LAST_USE_H

#include "../ClangTidyCheck.h"
#include "../utils/IncludeInserter.h"
#include "llvm/ADT/DenseMap.h"

namespace clang {

class CFG;
namespace tidy::performance {

/// A check that flags value parameters on last usages that can safely be moved,
/// because they are copied anyway.
///
/// For the user-facing documentation see:
/// http://clang.llvm.org/extra/clang-tidy/checks/performance/unnecessary-copy-on-last-use.html

class UnnecessaryCopyOnLastUseCheck : public ClangTidyCheck {
public:
  UnnecessaryCopyOnLastUseCheck(StringRef Name, ClangTidyContext *Context);
  UnnecessaryCopyOnLastUseCheck(UnnecessaryCopyOnLastUseCheck &&) = delete;
  UnnecessaryCopyOnLastUseCheck(const UnnecessaryCopyOnLastUseCheck &) = delete;
  UnnecessaryCopyOnLastUseCheck &
  operator=(UnnecessaryCopyOnLastUseCheck &&) = delete;
  UnnecessaryCopyOnLastUseCheck &
  operator=(const UnnecessaryCopyOnLastUseCheck &) = delete;
  ~UnnecessaryCopyOnLastUseCheck() override;

  bool isLanguageVersionSupported(const LangOptions &LangOpts) const override {
    return LangOpts.CPlusPlus11;
  }
  void registerMatchers(ast_matchers::MatchFinder *Finder) override;
  void check(const ast_matchers::MatchFinder::MatchResult &Result) override;
  void registerPPCallbacks(const SourceManager &SM, Preprocessor *PP,
                           Preprocessor *ModuleExpanderPP) override;
  void storeOptions(ClangTidyOptions::OptionMap &Opts) override;
  void onEndOfTranslationUnit() override;

private:
  CFG *getOrCreateCFG(const FunctionDecl *FD, ASTContext *C);

  utils::IncludeInserter Inserter;
  const std::vector<StringRef> BlockedTypes;
  const std::vector<StringRef> BlockedFunctions;

  // cfg cache
  llvm::DenseMap<const FunctionDecl *, std::unique_ptr<CFG>> CFGs;
};

} // namespace tidy::performance
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_PERFORMANCE_UNNECESSARY_COPY_ON_LAST_USE_H
