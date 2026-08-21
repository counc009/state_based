(* A generator can be paired with a RandomimzedState to explore a space of
 * states; rather than just randomly generating responses they track the
 * responses they have given and will lead us through exploring the entire
 * space (using some randomness so that we sample the space if we're not
 * sampling it fully. *)
open Value

module Generator (V : VALUE) : sig
  class generator : object
    method reset : bool
    method gen_attr : V.s -> string -> V.t
  end
end = struct
  (* We track the space to explore as a tree of unexplored nodes and nodes we've
   * explored for which we track how many of its children are nonempty (i.e.,
   * there are more options left in the space) and those options *)
  type 'v traverse_space =
    | Unexplored of {
        parent   : 'v traverse_space ref option }
    | Node of {
        parent   : 'v traverse_space ref option;
        nonempty : int;
        (* select maps [0, nonempty) to the index of a non-empty option *)
        select   : int array;
        options  : 'v iarray;
        children : 'v traverse_space array }

  type boolOrVal = Bool of bool | Value of V.t

  (* TODO: We may not actually need parent pointers, I think updating empty and
   * such is something we do in reset because then we have found the leaf nodes
   * and we can determine whether there is any use for further generation.
   * TODO: Either we keep tracking parents and we traverse upwards from cur at
   * reset or we track which choice we took and traverse downwards.
   * We can't update emptyness until reset because we don't know when the
   * traversal will end and the fact that we used a value X does not mean it
   * is empty unless it its child is never explored in which case that value
   * does not need to be explored again *)

  class generator = object (self)
    val mutable root = (Unexplored { parent = None } : boolOrVal traverse_space)
    val mutable cur = ref (Unexplored { parent = None })

    method reset =
      let () = cur <- ref root
      in match root with
      | Unexplored _ -> true
      | Node { nonempty; _ } -> nonempty > 0

    method gen_attr (where : V.s) (attr : string) =
      match !cur with
      | Unexplored { parent } ->
          let options = attr_gen where attr
          in let values = Iarray.of_list options
          in let nonempty = Iarray.length values
          in let children = Array.make nonempty (Unexplored { parent = cur })
          in failwith "TODO"
      | Node { nonempty; select; options; children; _ } ->
          let j = Random.int nonempty
          in let i = select.(j)
          in let () = cur <- ref children.(i)
          in let res =
            match Iarray.get options i with
            | Bool _  ->
                failwith "Asked to generate an attribute but found a bool"
            | Value v -> v
          in res
  end
end
