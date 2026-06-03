(* This file defines the built-in functions of the module language and provides
 * information necessary for their compilation. *)

module TargetAst = Target.Ast_Target

let lookup_builtin (nm : string) 
  : ((TargetAst.typ * TargetAst.typ * TargetAst.funct),
      string) result =
  match nm with
  | "cons_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ConsPath
      in Ok (arg_ty, res_ty, Target.ConsPath)
  | "path_of_string" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef PathOfString
      in Ok (arg_ty, res_ty, Target.PathOfString)
  | "string_of_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef StringOfPath
      in Ok (arg_ty, res_ty, Target.StringOfPath)
  | "ends_with_dir" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef EndsWithDir
      in Ok (arg_ty, res_ty, Target.EndsWithDir)
  | "base_name" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef BaseName
      in Ok (arg_ty, res_ty, Target.BaseName)
  | "path_from" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef PathFrom
      in Ok (arg_ty, res_ty, Target.PathFrom)
  | "add_ext" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef AddExt
      in Ok (arg_ty, res_ty, Target.AddExt)
  | "norm_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef NormalizePath
      in Ok (arg_ty, res_ty, Target.NormalizePath)
  | "can_become" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef CanBecome
      in Ok (arg_ty, res_ty, Target.CanBecome)
  | "to_lower" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ToLower
      in Ok (arg_ty, res_ty, Target.ToLower)
  | "substring" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef Substring
      in Ok (arg_ty, res_ty, Target.Substring)
  | "string_of_int" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef StringOfInt
      in Ok (arg_ty, res_ty, Target.StringOfInt)
  | "concat_line" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ConcatLine
      in Ok (arg_ty, res_ty, Target.ConcatLine)
  | "regex_of_literal" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef RegexOfLiteral
      in Ok (arg_ty, res_ty, Target.RegexOfLiteral)
  | "remove_matching_lines" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef RemoveMatchingLines
      in Ok (arg_ty, res_ty, Target.RemoveMatchingLines)
  | "replace_last_matching_expand" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ReplaceLastMatchingExpand
      in Ok (arg_ty, res_ty, Target.ReplaceLastMatchingExpand)
  | "replace_last_matching" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ReplaceLastMatching
      in Ok (arg_ty, res_ty, Target.ReplaceLastMatching)
  | "insert_line_matching" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef InsertNearMatching
      in Ok (arg_ty, res_ty, Target.InsertNearMatching)
  | "line_matches_regex" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef RegexLineMatches
      in Ok (arg_ty, res_ty, Target.RegexLineMatches)
  | "last_line_matching" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef GetLastLineMatch
      in Ok (arg_ty, res_ty, Target.GetLastLineMatch)

  | _ -> Error ("Undefined name " ^ nm)
