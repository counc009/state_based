module type BUILTIN = sig
  type lit
  type func
  type act

  val string_of_lit : lit -> string
end
