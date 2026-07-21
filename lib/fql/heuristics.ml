module Interp = Modules.Target.TargetInterp
module Target = Modules.Target.Ast_Target

module StringSet = Set.Make(String)
module IntSet = Set.Make(Int)

(* Generates the set of integers [0, n) *)
let rec int_range (n : int) : IntSet.t =
  if n <= 0
  then IntSet.empty
  else IntSet.add (n - 1) (int_range (n - 1))

let string_set = StringSet.of_list

(* Find the os_distribution string in the given state or returns None *)
let get_dist (s : Interp.state) : string option =
  let State (elems, _) = s
  in let env =
    (("env", Target.Primitive Unit), Target.Literal (Unit (), Unit))
  in match Interp.ElementMap.find_opt env elems with
  | Some (Positive (State (_, attrs))) ->
      let os_distribution =
        ("os_distribution", Target.Primitive String)
      in begin match Interp.AttributeMap.find_opt os_distribution attrs with
      | Some (Literal (String d, _)) -> Some d
      | _ -> None
      end
  | _ -> None

(* Returns the values of an attribute in the environment (if found) *)
let get_env_attr (s : Verifier.merged_diff) (attr : string) (ty : Target.typ)
  : int list Interp.ValueMap.t option =
  let MergedDiff (elems, _) = s
  in let env =
    (("env", Target.Primitive Unit), Target.Literal (Unit (), Unit))
  in match Interp.ElementMap.find_opt env elems with
  | None -> None
  | Some { diff; _ } ->
      let MergedDiff (_, attrs) = diff
      in Interp.AttributeMap.find_opt (attr, ty) attrs

(* Check that the users that are assumed to be present in r actually are
 * present given the set of users that exist, only checks the branches where
 * the os_distribution (in the query) matches if one is specified, this allows for
 * different configurations between different OSes. *)
let valid_users (users : StringSet.t) (dist : string option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; inits; _ } } ->
        let dist_matches =
          match dist with
          | None -> true
          | Some dist ->
            match get_dist base with
            | Some d -> d = dist
            | None -> false
        in if dist_matches
        then 
          let all_set = int_range branches
          in let MergedDiff (elems, _) = inits
          in let invalid_set =
            Interp.ElementMap.fold (fun ((elem, _), arg) binding invalid ->
              let { Verifier.pos; neg; _ } = binding
              in if elem <> "e_user"
              then invalid
              else
                match arg with
                | Literal (String nm, _) ->
                    if StringSet.mem nm users
                    then IntSet.union invalid (IntSet.of_list neg)
                    else IntSet.union invalid (IntSet.of_list pos)
                (* If we don't know the value of the user, the conservative
                 * approach is to accept it. Could explore other options but
                 * this cause issues when dealing with files with unknown
                 * owners *)
                | _ -> invalid
            ) elems IntSet.empty
          in not (IntSet.equal all_set invalid_set)
        else true
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

let valid_groups (groups : StringSet.t) (dist : string option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; inits; _ } } ->
        let dist_matches =
          match dist with
          | None -> true
          | Some dist ->
              match get_dist base with
              | Some d -> d = dist
              | None -> false
        in if dist_matches
        then 
          let all_set = int_range branches
          in let MergedDiff (elems, _) = inits
          in let invalid_set =
            Interp.ElementMap.fold (fun ((elem, _), arg) binding invalid ->
              let { Verifier.pos; neg; _ } = binding
              in if elem <> "e_group"
              then invalid
              else 
                match arg with
                | Literal (String nm, _) ->
                    if StringSet.mem nm groups
                    then IntSet.union invalid (IntSet.of_list neg)
                    else IntSet.union invalid (IntSet.of_list pos)
                | _ -> invalid
            ) elems IntSet.empty
          in not (IntSet.equal all_set invalid_set)
        else true
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

(* Checks that extra installed (i.e., final state) packages in the diff are
 * valid. Here pkgmgr is None or a pair of the OS distribution and package
 * manager *)
let valid_packages (packages : StringSet.t) (pkgmgr : (string * string) option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; finals; _ } } ->
        let dist_matches =
          match pkgmgr with
          | None -> true
          | Some (dist, _) ->
              match get_dist base with
              | Some d -> d = dist
              | None -> false
        in if not dist_matches
        then true
        else
          let all_set = int_range branches
          in let rec find_invalid
              (d : Verifier.merged_diff) (invalid : IntSet.t) : IntSet.t =
            let MergedDiff (elems, _) = d
            in Interp.ElementMap.fold (fun ((elem, _), arg) binding invalid ->
              let { Verifier.pos; neg; diff = nested } = binding
              in if elem <> "e_package"
              then find_invalid nested invalid
              else
                match arg with
                | Literal (String nm, _) ->
                    let manager_matches =
                      match pkgmgr with
                      | None -> true
                      | Some (_, mgr) ->
                          let MergedDiff (nested, _) = binding.diff
                          in Interp.ElementMap.mem 
                              ((mgr, Primitive Unit), Literal (Unit (), Unit))
                              nested
                    in if not manager_matches || StringSet.mem nm packages
                    then invalid
                    else
                      IntSet.union
                        (IntSet.union invalid (IntSet.of_list pos))
                        (IntSet.of_list neg)
                (* I don't know why we would be installing a mysterious
                 * package, so rejecting for now *)
                | _ -> 
                    IntSet.union
                      (IntSet.union invalid (IntSet.of_list pos))
                      (IntSet.of_list neg)
            ) elems invalid
          in let invalid_set = find_invalid finals IntSet.empty
          in not (IntSet.equal all_set invalid_set)
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

(* Checks that extra files that are assumed to exist do. Where specifies the OS
 * distribution and is true if referencing a remote file and false for a file
 * on the controller. The strict variable determines whether we reject files
 * whose paths are not literals *)
let valid_files (exist : StringSet.t) (not_exist: StringSet.t) (strict : bool)
  (where : (string * bool) option) (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; inits; _}; _ } ->
        let dist_matches =
          match where with
          | None -> true
          | Some (dist, _) ->
              match get_dist base with
              | Some d -> d = dist
              | None -> false
        in if not dist_matches
        then true
        else
          let all_set = int_range branches
          in let MergedDiff (elems, _) = inits
          in let invalid_set =
            Interp.ElementMap.fold (fun ((elem, _), arg) binding invalid ->
              let { Verifier.pos; neg; _ } = binding
              in if elem <> "fs" || not (List.is_empty pos || List.is_empty neg)
              then invalid
              else
                match arg with
                | Pair (Literal (Path p, _), Constructor (_, which, _), _) ->
                    let sys_match =
                      match where with
                      | None -> true
                      | Some (_, sys) -> sys = which
                    in if not sys_match
                    then invalid
                    else if StringSet.mem p exist
                    then IntSet.union invalid (IntSet.of_list neg)
                    else if StringSet.mem p not_exist
                    then IntSet.union invalid (IntSet.of_list pos)
                    else (* We don't know if the file exists or not *)
                      (* If we have both positive and negative branches then
                       * none of these branches are invalid, because the file
                       * can be in either state and so there is some branch we
                       * can use. But, if there are only positive or only
                       * negative branches then those branches are invalid
                       * because they rely on a file we shouldn't care about the
                       * existance of. There's a temptation a say as long as
                       * some other branch doesn't rely on this file then these
                       * branches are not invalid, but that's only the case if
                       * those other branches do not have their own invalid
                       * file assumptions. For example, if branch 1 relies on
                       * file a existing and branch 2 relies on file b existing
                       * then the program is invalid if a and b are both
                       * irrelevent because if neither exists neither branch
                       * works. By adding the branches to the set here and then
                       * checking at the end of all branches are collected, we
                       * handle this appropriately. *)
                      if List.is_empty pos
                      then IntSet.union invalid (IntSet.of_list neg)
                      else if List.is_empty neg
                      then IntSet.union invalid (IntSet.of_list pos)
                      else invalid
                | _ ->
                    if not strict
                    then invalid
                    else
                      IntSet.union
                        (IntSet.union invalid (IntSet.of_list pos))
                        (IntSet.of_list neg)
            ) elems IntSet.empty
          in not (IntSet.equal all_set invalid_set)
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

let get_not_excluded (hosts: string) (branches : int) inits
  (bools : Verifier.Unifier.merged_bool Interp.ValueMap.t) =
  let all_set = int_range branches
  in match get_env_attr inits "hostname" (Primitive String) with
  | None -> all_set
  | Some vs ->
      Interp.ValueMap.fold (fun hostname ns res ->
        let host_included =
          Target.Function (HostIncluded,
            Pair (hostname,
              Literal (String hosts, String),
              Product (Primitive String, Primitive String)),
            Primitive Bool)
        in match Interp.ValueMap.find_opt host_included bools with
        | None -> res
        | Some { f; _ } -> 
            IntSet.diff res 
              (IntSet.inter (IntSet.of_list ns) (IntSet.of_list f))
      ) vs all_set

(* Checks that the diff does not contain a reboot of the system, meaning it
 * cannot reboot the system unless the query does as well.
 * Because we are checking that we do not perform a certain action, another
 * way a program could satisfy this is by assuming that we don't run the play
 * at all by assuming the hostname is not included in the hosts; to avoid not
 * rejecting a program because of this assumption, we only need the reboot to
 * occur on the branches where we don't assume the host is excluded *)
let valid_reboot (hosts : string) (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { diff = { branches; constraints = { bools; _ }; 
                           inits; finals }; _ } ->
        let not_excluded = get_not_excluded hosts branches inits bools
        in begin match get_env_attr finals "last_reboot" (Primitive Int) with
        | None -> true
        | Some vs ->
            let which_set =
              Interp.ValueMap.fold (fun _ ns set ->
                IntSet.union set (IntSet.of_list ns))
                vs IntSet.empty
            in if IntSet.subset not_excluded which_set
            then false
            else true
        end
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

(* Checks that the diff does not contain any writes to files (i.e., it does not
 * write to any files not written to by the query. *)
let valid_writes (hosts : string) (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { diff = { branches; constraints = { bools; _ };
                           inits; finals }; _ } ->
      let not_excluded = get_not_excluded hosts branches inits bools
      in let MergedDiff (elems, _) = finals
      in let invalid_set =
        Interp.ElementMap.fold (fun ((elem, _), _)
          { Verifier.diff = MergedDiff (_, attrs); _ } invalid ->
            if elem <> "fs"
            then invalid
            else
              let write =
                let fs_type =
                  Interp.AttributeMap.filter 
                    (fun (attr, _) _ -> attr = "fs_type") attrs
                in Interp.AttributeMap.choose_opt fs_type
              in match write with
              | None -> (* Not written *) invalid
              | Some (_, vs) ->
                  let do_write =
                    Interp.ValueMap.fold (fun _ ns write ->
                      IntSet.union write (IntSet.of_list ns))
                      vs IntSet.empty
                  in IntSet.union invalid do_write
        ) elems IntSet.empty
      in not (IntSet.subset not_excluded invalid_set)
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r
