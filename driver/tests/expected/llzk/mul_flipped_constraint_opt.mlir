module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = felt.neg %0 : !felt.type
      %2 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      constrain.eq %1, %2 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      %4 = felt.mul %0, %2 : !felt.type, !felt.type
      constrain.eq %3, %4 : !felt.type, !felt.type
      constrain.eq %0, %arg1 : !felt.type, !felt.type
      %5 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %3, %5 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @adv_1_0 : !felt.type
    struct.member @adv_2_0 : !felt.type
  }
}
