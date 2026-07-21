(* This file defines the built-in functions of the module language and provides
 * information necessary for their compilation. *)

module TargetAst = Target.Ast_Target

(* Explanation of return type:
 * - Error msg - indicates that nm is not a built-in function
 * - Ok func_info - indicates that nm is a built-in function.
 *   If func_info arg_ty is
 *   + Error msg - indicates that the function does not work on an argument of
 *     type arg_ty
 *   + Ok (res_ty, func) - indicates that the function does work on the
 *     argument type and will produce a res_ty and can be compiled to func
 * This definition allows us to check for the existance of a built-in before
 * compiling the argument but still handle polymorphic built-in functions *)
let lookup_builtin (nm : string)
  : (TargetAst.typ -> (TargetAst.typ * TargetAst.funct, string) result, 
      string) result =

  let with_arg_ty (argTy : TargetAst.typ) resTy func ty =
    if argTy = ty
    then Ok (resTy, func)
    else Error ("Incorrect type for function " ^ nm)

  in let from_target func =
    let (arg_ty, res_ty, _) = TargetAst.funcDef func
    in Ok (with_arg_ty arg_ty res_ty func)

  in match nm with
  | "add_ext"               -> from_target Target.AddExt
  | "base_name"             -> from_target Target.BaseName
  | "can_become"            -> from_target Target.CanBecome
  | "concat_line"           -> from_target Target.ConcatLine
  | "cons_path"             -> from_target Target.ConsPath
  | "contains_line"         -> from_target Target.ContainsLine
  | "ends_with_dir"         -> from_target Target.EndsWithDir
  | "find_block"            -> from_target Target.FindBlock
  | "insert_line_matching"  -> from_target Target.InsertNearMatching
  | "last_line_matching"    -> from_target Target.GetLastLineMatch
  | "line_matches_regex"    -> from_target Target.RegexLineMatches
  | "norm_path"             -> from_target Target.NormalizePath
  | "path_from"             -> from_target Target.PathFrom
  | "path_of_string"        -> from_target Target.PathOfString
  | "regex_of_literal"      -> from_target Target.RegexOfLiteral
  | "remove_block"          -> from_target Target.RemoveBlock
  | "remove_matching_lines" -> from_target Target.RemoveMatchingLines
  | "replace_block"         -> from_target Target.ReplaceBlock
  | "replace_last_matching" -> from_target Target.ReplaceLastMatching
  | "replace_last_matching_expand"
                            -> from_target Target.ReplaceLastMatchingExpand
  | "string_of_int"         -> from_target Target.StringOfInt
  | "string_of_path"        -> from_target Target.StringOfPath
  | "string_subst"          -> from_target Target.StringSubst
  | "substring"             -> from_target Target.Substring
  | "to_lower"              -> from_target Target.ToLower

  | "len" ->
      Ok begin function
      | Named (List e) -> Ok (Primitive Int, Target.ListLength e)
      | _ -> Error ("Incorrect type for function len")
      end

  | _ -> Error ("Undefined name " ^ nm)
