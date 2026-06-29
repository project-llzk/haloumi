module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type
    struct.member @out_1 : !felt.type
    struct.member @out_2 : !felt.type
    function.def @compute() -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      function.return
    }
  }
}
