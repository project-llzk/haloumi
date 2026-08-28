module attributes {llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>>} {
  struct.def @Main {
    function.def @compute(%arg0: !felt.type, %arg1: !felt.type, %arg2: !felt.type) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type, %arg2: !felt.type, %arg3: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      function.return
    }
  }
}
