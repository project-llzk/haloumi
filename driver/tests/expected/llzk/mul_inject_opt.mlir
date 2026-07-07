module attributes { llzk.lang = "halo2"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_1 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_2 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1000 = felt.const  1000 <"bn254">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = felt.neg %0 : !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = felt.mul %0, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %3, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %6 = felt.neg %5 : !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %8 = felt.mul %5, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %11 = felt.neg %10 : !felt.type<"bn254">
      %12 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %11, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = felt.mul %10, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %14 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %13, %14 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %5, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %10, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %4, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %16 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %9, %16 : !felt.type<"bn254">, !felt.type<"bn254">
      %17 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %14, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %18 = bool.cmp lt(%0, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %18
      %19 = bool.cmp ge(%2, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %19
      %20 = bool.cmp lt(%5, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %20
      %21 = bool.cmp ge(%7, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %21
      %22 = bool.cmp lt(%10, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %22
      %23 = bool.cmp ge(%12, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      bool.assert %23
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254">
    struct.member @adv_0_1 : !felt.type<"bn254">
    struct.member @adv_1_0 : !felt.type<"bn254">
    struct.member @adv_0_2 : !felt.type<"bn254">
    struct.member @adv_0_3 : !felt.type<"bn254">
    struct.member @adv_1_2 : !felt.type<"bn254">
    struct.member @adv_0_4 : !felt.type<"bn254">
    struct.member @adv_0_5 : !felt.type<"bn254">
    struct.member @adv_1_4 : !felt.type<"bn254">
  }
}
