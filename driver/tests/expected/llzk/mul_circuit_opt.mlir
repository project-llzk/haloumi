module attributes { llzk.lang = "halo2"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = felt.neg %0 : !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254"> 
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = felt.mul %0, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %5, %6 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %6, %10 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254"> 
    struct.member @adv_1_0 : !felt.type<"bn254"> 
    struct.member @adv_2_0 : !felt.type<"bn254"> 
  }
}

