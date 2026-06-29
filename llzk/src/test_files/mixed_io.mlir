module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    struct.member @out_1 : !felt.type {llzk.pub}
    struct.member @out_2 : !felt.type
    struct.member @out_3 : !felt.type
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type, %arg3: !felt.type, %arg4: !felt.type) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}, %arg3: !felt.type, %arg4: !felt.type, %arg5: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      function.return
    }
  }
}
