open Ast
module Target = Modules.Target.Ast_Target

type context = { os: ansible_os list option }

module type Knowledge_Base = sig
  type repoInfo = { files: Target.expr; contents: Target.expr -> Target.expr }
  val repoDef : context -> ParseTree.vals -> args -> (repoInfo, string) result

  val fileDef : context -> ParseTree.vals -> args -> (path, string) result
  val filesDef : context -> ParseTree.vals -> args -> (paths, string) result
  val dirDef : context -> ParseTree.vals -> args -> (path, string) result

  val requirementDef : context -> ParseTree.vals -> (Ast.cond, string) result

  val pkgDef : context -> ParseTree.vals -> args -> (Ast.pkg, string) result
  val serviceDef : context -> ParseTree.vals -> args -> (string, string) result
end
