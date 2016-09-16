// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <http://unlicense.org/>

#include <cassert>
#include <map>
#include <vector>

#define __STDC_CONSTANT_MACROS
#define __STDC_LIMIT_MACROS
#include <llvm-c/Core.h>

extern "C" {
#include <mpc/mpc.h>
}

#define AST_ASSERT(cond, message) assert(cond &&message)
#define AST_ASSERT_STREQ(str1, str2, message)                                  \
  AST_ASSERT(0 == strcmp(str1, str2), message)

namespace {
LLVMTypeRef LLVMGetFunctionTypeEXT(LLVMValueRef function) {
  // in the LLVM C API, TypeOf returns a pointer to the function type, rather
  // than the function type itself, thus we need to also use get element type
  return LLVMGetElementType(LLVMTypeOf(function));
}

bool strendEXT(const char *string, const char *suffix) {
  // assuming non-null arguments
  const size_t stringLength = strlen(string);
  const size_t suffixLength = strlen(suffix);

  if (suffixLength > stringLength) {
    return false;
  } else {
    return 0 ==
           strncmp(string + stringLength - suffixLength, suffix, suffixLength);
  }
}
}

const char *src = "i32 foo(i32 x) {\n"
                  "  i32 y = x * 5;\n"
                  "  y = y + 42;\n"
                  "  return y;\n"
                  "}\n"
                  "i32 main() {\n"
                  "  return foo(13);\n"
                  "}\n";

int parse(const char *filename, const char *source, mpc_result_t *out_result) {
  mpc_parser_t *Ident = mpc_new("ident");
  mpc_parser_t *Number = mpc_new("literal");
  mpc_parser_t *Factor = mpc_new("factor");
  mpc_parser_t *Term = mpc_new("term");
  mpc_parser_t *Lexp = mpc_new("lexp");
  mpc_parser_t *Stmt = mpc_new("stmt");
  mpc_parser_t *Type = mpc_new("type");
  mpc_parser_t *Typeident = mpc_new("typeident");
  mpc_parser_t *Args = mpc_new("args");
  mpc_parser_t *Body = mpc_new("body");
  mpc_parser_t *Procedure = mpc_new("procedure");
  mpc_parser_t *Lang = mpc_new("lang");

  mpc_err_t *err = mpca_lang(
      MPCA_LANG_DEFAULT,
      " ident     : /[a-zA-Z_][a-zA-Z0-9_]*/ ;                           \n"
      " literal   : /[0-9]+(\\.[0-9]+)?((e|E)(-|\\+)?[0-9]+)?/ ;         \n"
      "                                                                  \n"
      " type      : (\"i1\" | /(i|u)(8|16|32|64)/ | /f(16|32|64)/) ;     \n"
      " typeident : <type> <ident> ;                                     \n"
      "                                                                  \n"
      " factor    : <literal>                                            \n"
      "           | <ident> '(' <lexp>? (',' <lexp>)* ')'                \n"
      "           | <ident> ;                                            \n"
      "                                                                  \n"
      " term      : <factor> (('*' | '/' | '%') <factor>)* ;             \n"
      " lexp      : <term> (('+' | '-') <term>)* ;                       \n"
      "                                                                  \n"
      " stmt      : \"return\" <lexp>? ';'                               \n"
      "           | <ident> '(' <ident>? (',' <ident>)* ')' ';'          \n"
      "           | <typeident> ('=' <lexp>)? ';'                        \n"
      "           | <ident> '=' <lexp> ';' ;                             \n"
      "                                                                  \n"
      " args      : <typeident>? (',' <typeident>)* ;                    \n"
      " body      : '{' <stmt>* '}' ;                                    \n"
      " procedure : <type> <ident> '(' <args> ')' <body> ;               \n"
      " lang      : /^/ ((<typeident> ';') |  <procedure>)* /$/ ;        \n",
      Ident, Number, Factor, Term, Lexp, Stmt, Typeident, Type, Args, Body,
      Procedure, Lang, NULL);

  if (err != NULL) {
    mpc_err_print(err);
    mpc_err_delete(err);
    exit(1);
  }

  const int result = mpc_parse(filename, source, Lang, out_result);

  mpc_cleanup(12, Ident, Number, Factor, Term, Lexp, Stmt, Typeident, Type,
              Args, Body, Procedure, Lang);

  return result;
}

namespace {
struct MyStringCompare {
  bool operator()(const char *lhs, const char *rhs) const {
    return 0 > strcmp(lhs, rhs);
  }
};
}

template <typename T> using NeilVector = std::vector<T>;
template <typename T>
using NeilMap = std::map<const char *, T, MyStringCompare>;

struct ASTLowering {
  explicit ASTLowering(const char *fileName)
      : module(LLVMModuleCreateWithName(fileName)),
        builder(LLVMCreateBuilder()) {
    typeTable["i8"] = LLVMInt8Type();
    typeTable["i16"] = LLVMInt16Type();
    typeTable["i32"] = LLVMInt32Type();
    typeTable["i64"] = LLVMInt64Type();
    typeTable["f16"] = LLVMHalfType();
    typeTable["f32"] = LLVMFloatType();
    typeTable["f64"] = LLVMDoubleType();
  }

  LLVMValueRef lower_ast_node(mpc_ast_t *const ast, LLVMTypeRef type) {
    if (strendEXT(ast->tag, "term|>")) {
      return lower_term(ast, type);
    } else if (strendEXT(ast->tag, "factor|>")) {
      return lower_factor(ast, type);
    } else if (strendEXT(ast->tag, "lexp|>")) {
      return lower_lexp(ast, type);
    } else if (strendEXT(ast->tag, "literal|regex")) {
      return lower_literal(ast, type);
    } else if (strendEXT(ast->tag, "ident|regex")) {
      return lower_ident(ast, type);
    } else {
      AST_ASSERT(false, "unknown ast node detected");
      return nullptr;
    }
  }

  LLVMValueRef lower_ident(mpc_ast_t *const ast, LLVMTypeRef type) {
    AST_ASSERT(
        nullptr != symbolTable[ast->contents],
        "expected ident AST node to be a valid symbol in the symbol table");

    LLVMValueRef value = symbolTable[ast->contents];

    if (LLVMIsAAllocaInst(value)) {
      return LLVMBuildLoad(builder, value, "");
    } else {
      return value;
    }
  }

  LLVMValueRef lower_factor(mpc_ast_t *const ast, LLVMTypeRef type) {
    const int lastChild = ast->children_num - 1;

    // if our factor is actually a function call
    if ((0 == strcmp("ident|regex", ast->children[0]->tag)) &&
        (0 == strcmp("char", ast->children[1]->tag)) &&
        (0 == strcmp("(", ast->children[1]->contents)) &&
        (0 == strcmp("char", ast->children[lastChild]->tag)) &&
        (0 == strcmp(")", ast->children[lastChild]->contents))) {
      mpc_ast_t *name = ast->children[0];

      LLVMValueRef calledFunction = symbolTable[name->contents];

      AST_ASSERT(nullptr != calledFunction, "expected factor AST node's first "
                                            "child to be a known function to "
                                            "call");

      LLVMTypeRef calledFunctionType = LLVMGetFunctionTypeEXT(calledFunction);

      AST_ASSERT(LLVMFunctionValueKind == LLVMGetValueKind(calledFunction),
                 "expected ");

      NeilVector<LLVMTypeRef> parameterTypes(
          LLVMCountParamTypes(calledFunctionType));

      LLVMGetParamTypes(calledFunctionType, parameterTypes.data());

      AST_ASSERT(parameterTypes.size() == lastChild - 2,
                 "the number of parameters the function call expected did not "
                 "match the number provided");

      NeilVector<LLVMValueRef> arguments;

      for (int i = 2; i < lastChild; i++) {
        arguments.push_back(
            lower_ast_node(ast->children[i], parameterTypes[i - 2]));
      }

      LLVMValueRef call = LLVMBuildCall(builder, calledFunction,
                                        arguments.data(), arguments.size(), "");

      return call;
    }

    AST_ASSERT(false, "unhandled factor AST node");

    return nullptr;
  }

  LLVMValueRef lower_term(mpc_ast_t *const ast, LLVMTypeRef type) {
    AST_ASSERT(0 == ((ast->children_num - 1) % 2),
               "expected (N * 2) + 1 children in our term AST node");

    LLVMValueRef result = lower_ast_node(ast->children[0], type);

    for (int i = 1; i < ast->children_num; i += 2) {
      mpc_ast_t *const operation = ast->children[i];

      AST_ASSERT_STREQ("char", operation->tag,
                       "expected term AST node's child to be a character");

      LLVMValueRef rhs = lower_ast_node(ast->children[i + 1], type);

      switch (operation->contents[0]) {
      case '*':
        switch (LLVMGetTypeKind(type)) {
        default:
          AST_ASSERT(false, "unknown type for term AST node");
        case LLVMHalfTypeKind:
        case LLVMFloatTypeKind:
        case LLVMDoubleTypeKind:
          result = LLVMBuildFMul(builder, result, rhs, "");
          break;
        case LLVMIntegerTypeKind:
          result = LLVMBuildMul(builder, result, rhs, "");
          break;
        }
        break;
      case '/':
        switch (LLVMGetTypeKind(type)) {
        default:
          AST_ASSERT(false, "unknown type for term AST node");
        case LLVMHalfTypeKind:
        case LLVMFloatTypeKind:
        case LLVMDoubleTypeKind:
          result = LLVMBuildFDiv(builder, result, rhs, "");
          break;
        case LLVMIntegerTypeKind:
          result = LLVMBuildSDiv(builder, result, rhs, "");
          break;
        }
        break;
      case '%':
        switch (LLVMGetTypeKind(type)) {
        default:
          AST_ASSERT(false, "unknown type for term AST node");
        case LLVMHalfTypeKind:
        case LLVMFloatTypeKind:
        case LLVMDoubleTypeKind:
          result = LLVMBuildFRem(builder, result, rhs, "");
          break;
        case LLVMIntegerTypeKind:
          result = LLVMBuildSRem(builder, result, rhs, "");
          break;
        }
        break;
      }
    }

    return result;
  }

  LLVMValueRef lower_literal(mpc_ast_t *const ast, LLVMTypeRef type) {
    switch (LLVMGetTypeKind(type)) {
    default:
      AST_ASSERT(false, "unknown type for literal AST node");
    case LLVMHalfTypeKind:
    case LLVMFloatTypeKind:
    case LLVMDoubleTypeKind:
      return LLVMConstRealOfString(type, ast->contents);
    case LLVMIntegerTypeKind:
      return LLVMConstIntOfString(type, ast->contents, 10);
    }
  }

  LLVMValueRef lower_lexp(mpc_ast_t *const ast, LLVMTypeRef type) {
    AST_ASSERT(0 == ((ast->children_num - 1) % 2),
               "expected (N * 2) + 1 children in our lexp AST node");

    LLVMValueRef result = lower_ast_node(ast->children[0], type);

    for (int i = 1; i < ast->children_num; i += 2) {
      mpc_ast_t *const operation = ast->children[i];

      AST_ASSERT_STREQ("char", operation->tag,
                       "expected lexp AST node's child to be a character");

      LLVMValueRef rhs = lower_ast_node(ast->children[i + 1], type);

      switch (operation->contents[0]) {
      case '+':
        switch (LLVMGetTypeKind(type)) {
        default:
          AST_ASSERT(false, "unknown type for lexp AST node");
        case LLVMHalfTypeKind:
        case LLVMFloatTypeKind:
        case LLVMDoubleTypeKind:
          result = LLVMBuildFAdd(builder, result, rhs, "");
          break;
        case LLVMIntegerTypeKind:
          result = LLVMBuildAdd(builder, result, rhs, "");
          break;
        }
        break;
      case '-':
        switch (LLVMGetTypeKind(type)) {
        default:
          AST_ASSERT(false, "unknown type for lexp AST node");
        case LLVMHalfTypeKind:
        case LLVMFloatTypeKind:
        case LLVMDoubleTypeKind:
          result = LLVMBuildFSub(builder, result, rhs, "");
          break;
        case LLVMIntegerTypeKind:
          result = LLVMBuildSub(builder, result, rhs, "");
          break;
        }
        break;
      }
    }

    return result;
  }

  LLVMValueRef lower_return(mpc_ast_t *const ast) {
    AST_ASSERT(2 <= ast->children_num,
               "expected return AST node to have at least two children");

    LLVMTypeRef returnType =
        LLVMGetReturnType(LLVMGetFunctionTypeEXT(function));

    // if we have two children, we are trying to return nothing (void return)
    if (2 == ast->children_num) {
      AST_ASSERT(
          LLVMVoidTypeKind == LLVMGetTypeKind(returnType),
          "return AST node returning nothing when the return type is not void");

      AST_ASSERT_STREQ(
          "char", ast->children[1]->tag,
          "expected return AST node's second child to be a character");

      AST_ASSERT_STREQ(
          ";", ast->children[1]->contents,
          "expected return AST node's second child to be the character ';'");

      return LLVMBuildRetVoid(builder);
    } else {
      AST_ASSERT_STREQ(
          "char", ast->children[2]->tag,
          "expected return AST node's third child to be a character");

      AST_ASSERT_STREQ(
          ";", ast->children[2]->contents,
          "expected return AST node's third child to be the character ';'");

      LLVMValueRef result = lower_ast_node(ast->children[1], returnType);

      return LLVMBuildRet(builder, result);
    }
  }

  int lower_statement(mpc_ast_t *const ast) {
    AST_ASSERT(1 <= ast->children_num,
               "expected statement AST node to have at least one child");

    if ((0 == strcmp("string", ast->children[0]->tag)) &&
        (0 == strcmp("return", ast->children[0]->contents))) {
      lower_return(ast);
    } else if (0 == strcmp("typeident|>", ast->children[0]->tag)) {
      mpc_ast_t *const typeident = ast->children[0];
      AST_ASSERT(2 == typeident->children_num,
                 "expected type identifier to have two children");

      AST_ASSERT_STREQ("type|regex", typeident->children[0]->tag,
                       "expected type identifier's first child to be a type");

      AST_ASSERT(nullptr != typeTable[typeident->children[0]->contents],
                 "expected type to be in typeTable");

      LLVMTypeRef type = typeTable[typeident->children[0]->contents];

      AST_ASSERT_STREQ(
          "ident|regex", typeident->children[1]->tag,
          "expected type identifier's second child to be an identifier");

      AST_ASSERT(
          0 == symbolTable.count(typeident->children[1]->contents),
          "inserting symbol into the symbol table failed because a symbol was "
          "already present for the given symbol name");

      // we need to create a function-local memory location for our variable.
      // For this we'll use the stack (alloca!)
      LLVMValueRef value =
          LLVMBuildAlloca(builder, type, typeident->children[1]->contents);

      symbolTable[typeident->children[1]->contents] = value;
      symbolCleanup.push_back(typeident->children[1]->contents);

      // if we have more than two children, our typeident has an initializer
      if (2 < ast->children_num) {
        AST_ASSERT_STREQ("char", ast->children[1]->tag,
                         "expected the second child of the statement AST node "
                         "to be a character");
        AST_ASSERT_STREQ("=", ast->children[1]->contents,
                         "expected the second child of the statement AST node "
                         "to be the character '='");

        LLVMValueRef initializer = lower_ast_node(ast->children[2], type);

        LLVMBuildStore(builder, initializer, value);

        AST_ASSERT_STREQ("char", ast->children[3]->tag,
                         "expected the fourth child of the statement AST node "
                         "to be a character");
        AST_ASSERT_STREQ(";", ast->children[3]->contents,
                         "expected the fourth child of the statement AST node "
                         "to be the character ';'");
      } else {
        AST_ASSERT_STREQ("char", ast->children[1]->tag,
                         "expected the second child of the statement AST node "
                         "to be a character");
        AST_ASSERT_STREQ(";", ast->children[1]->contents,
                         "expected the second child of the statement AST node "
                         "to be the character ';'");
      }
    } else if ((0 == strcmp("ident|regex", ast->children[0]->tag)) &&
               (0 == strcmp("char", ast->children[1]->tag)) &&
               (0 == strcmp("=", ast->children[1]->contents))) {
      // we are assigning a new value to an identifier!
      AST_ASSERT(nullptr != symbolTable[ast->children[0]->contents],
                 "expected identifier to have an existing symbol in the symbol "
                 "table!");
      LLVMValueRef lhs = symbolTable[ast->children[0]->contents];

      AST_ASSERT(nullptr != LLVMIsAAllocaInst(lhs),
                 "expected symbol we are storing to to be an alloca");
      LLVMValueRef rhs =
          lower_ast_node(ast->children[2], LLVMGetElementType(LLVMTypeOf(lhs)));

      LLVMBuildStore(builder, rhs, lhs);
    } else {
      AST_ASSERT(false, "unknown statement AST node");
    }

    return 0;
  }

  int lower_function_body(mpc_ast_t *const ast) {
    LLVMBasicBlockRef block = LLVMAppendBasicBlock(function, "");

    LLVMPositionBuilderAtEnd(builder, block);

    AST_ASSERT(
        3 <= ast->children_num,
        "expected function body AST node to have at least three children");

    AST_ASSERT_STREQ(
        "char", ast->children[0]->tag,
        "expected function body AST node's first child to be a character");

    AST_ASSERT_STREQ("{", ast->children[0]->contents,
                     "expected function body AST node's first child to be the "
                     "character '{'");

    const int lastChild = ast->children_num - 1;

    AST_ASSERT_STREQ(
        "char", ast->children[lastChild]->tag,
        "expected function body AST node's last child to be a character");

    AST_ASSERT_STREQ(
        "}", ast->children[lastChild]->contents,
        "expected function body AST node's last child to be the character '}'");

    for (int i = 1; i < lastChild; i++) {
      AST_ASSERT_STREQ(
          "stmt|>", ast->children[i]->tag,
          "expected function body AST node's child to be a statement");

      lower_statement(ast->children[i]);
    }

    return 0;
  }

  int lower_function(mpc_ast_t *const ast) {
    AST_ASSERT(5 <= ast->children_num,
               "expected function AST node to have at least five children");

    mpc_ast_t *const type = ast->children[0];

    AST_ASSERT_STREQ("type|regex", type->tag,
                     "expected function AST node's first child to be a type");

    LLVMTypeRef returnType = typeTable[type->contents];

    AST_ASSERT(nullptr != returnType,
               "expected return type of function to be a known type");

    mpc_ast_t *const name = ast->children[1];

    AST_ASSERT_STREQ(
        "ident|regex", name->tag,
        "expected function AST node's second child to be an identifier");

    mpc_ast_t *const openingParen = ast->children[2];
    AST_ASSERT_STREQ(
        "char", openingParen->tag,
        "expected function AST node's third child to be a character");
    AST_ASSERT_STREQ(
        "(", openingParen->contents,
        "expected function AST node's third child to be the character '('");

    // an AST node that the body of the function will (eventually) reside in
    mpc_ast_t *body = nullptr;

    NeilVector<LLVMTypeRef> paramTypes;
    NeilVector<const char *> paramNames;

    for (int i = 3; i < ast->children_num; i++) {
      if ((0 == strcmp("char", ast->children[i]->tag)) &&
          (0 == strcmp(")", ast->children[i]->contents))) {
        body = ast->children[i + 1];
        break;
      }

      AST_ASSERT_STREQ(
          "args|typeident|>", ast->children[i]->tag,
          "expected function AST node's child to be a type identifier");

      AST_ASSERT(2 == ast->children[i]->children_num,
                 "expected type identifier node to have two children");

      mpc_ast_t *const type = ast->children[i]->children[0];

      AST_ASSERT_STREQ(
          "type|regex", type->tag,
          "expected type identifier node's first child to be a type");

      AST_ASSERT(nullptr != typeTable[type->contents],
                 "expected type identifier node to have a known type");

      mpc_ast_t *const name = ast->children[i]->children[1];

      AST_ASSERT_STREQ(
          "ident|regex", name->tag,
          "expected type identifier node's second child to be an identifier");

      paramTypes.push_back(typeTable[type->contents]);
      paramNames.push_back(name->contents);
    }

    AST_ASSERT(nullptr != body,
               "expected function AST node to have a function body child");

    AST_ASSERT_STREQ(
        "body|>", body->tag,
        "expected function AST node's last child to be the function body");

    LLVMTypeRef functionType = LLVMFunctionType(returnType, paramTypes.data(),
                                                paramTypes.size(), false);

    function = LLVMAddFunction(module, name->contents, functionType);

    const unsigned numParameters = LLVMCountParams(function);

    NeilVector<LLVMValueRef> params(numParameters, nullptr);

    LLVMGetParams(function, params.data());

    for (unsigned i = 0; i < numParameters; i++) {
      LLVMSetValueName(params[i], paramNames[i]);
    }

    // record the new function in the symbol table
    AST_ASSERT(
        0 == symbolTable.count(name->contents),
        "function symbol has the same name as an existing tracked symbol");
    symbolTable[name->contents] = function;

    // record that each parameter is in the symbol table too
    for (unsigned i = 0; i < numParameters; i++) {

      AST_ASSERT(0 == symbolTable.count(paramNames[i]),
                 "function's parameter has the same name as an existing "
                 "tracked symbol");
      symbolTable[paramNames[i]] = params[i];
      symbolCleanup.push_back(paramNames[i]);
    }

    const int result = lower_function_body(body);

    // remove any symbols that are local to the function. This includes
    // parameters to the function, and identifiers declared in the body of the
    // function.
    for (auto symbol : symbolCleanup) {
      symbolTable.erase(symbol);
    }

    symbolCleanup.clear();

    return result;
  }

  int lower(mpc_ast_t *const ast) {
    AST_ASSERT_STREQ(">", ast->tag, "expected root AST node to be '>'");

    AST_ASSERT_STREQ(
        "regex", ast->children[0]->tag,
        "expected first child of root node to be a regex for file start '^'");

    AST_ASSERT_STREQ(
        "regex", ast->children[ast->children_num - 1]->tag,
        "expected last child of root node to be a regex for file end '$'");

    for (int i = 1, e = ast->children_num - 1; i < e; i++) {
      AST_ASSERT_STREQ("procedure|>", ast->children[i]->tag,
                       "expected child of root node to be a procedure");

      lower_function(ast->children[i]);
    }

    return 0;
  }

  LLVMModuleRef module;

private:
  LLVMBuilderRef builder;
  LLVMValueRef function;
  NeilMap<LLVMTypeRef> typeTable;
  NeilMap<LLVMValueRef> symbolTable;
  NeilVector<const char *> symbolCleanup;
};

int mpc2llvm(const char *filename, mpc_ast_t *ast) {
  ASTLowering lowering(filename);

  lowering.lower(ast);

  LLVMDumpModule(lowering.module);

  return 0;
}

int main() {
  const char *filename = "foo.neil";
  mpc_result_t result;

  if (parse(filename, src, &result)) {
    mpc_ast_print((mpc_ast_t *)result.output);

    const int r = mpc2llvm(filename, (mpc_ast_t *)result.output);

    mpc_ast_delete((mpc_ast_t *)result.output);

    if (r) {
      printf("mpc -> llvm error!\n");
      return -1;
    }

    return 0;
  } else {
    mpc_err_print(result.error);
    mpc_err_delete(result.error);

    return -1;
  }
}
