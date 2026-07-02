module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    struct.member @out_1 : !felt.type<"f"> {llzk.pub}
    struct.member @out_2 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1000 = felt.const  1000 <"f">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = felt.neg %0 : !felt.type<"f">
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %1, %2 : !felt.type<"f">, !felt.type<"f">
      %3 = felt.mul %0, %2 : !felt.type<"f">, !felt.type<"f">
      %4 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %3, %4 : !felt.type<"f">, !felt.type<"f">
      %5 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %6 = felt.neg %5 : !felt.type<"f">
      %7 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %6, %7 : !felt.type<"f">, !felt.type<"f">
      %8 = felt.mul %5, %7 : !felt.type<"f">, !felt.type<"f">
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %8, %9 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %11 = felt.neg %10 : !felt.type<"f">
      %12 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %11, %12 : !felt.type<"f">, !felt.type<"f">
      %13 = felt.mul %10, %12 : !felt.type<"f">, !felt.type<"f">
      %14 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %13, %14 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %0, %arg1 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %5, %arg1 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %10, %arg1 : !felt.type<"f">, !felt.type<"f">
      %15 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %4, %15 : !felt.type<"f">, !felt.type<"f">
      %16 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %9, %16 : !felt.type<"f">, !felt.type<"f">
      %17 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %14, %17 : !felt.type<"f">, !felt.type<"f">
      %18 = bool.cmp lt(%0, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %18
      %19 = bool.cmp ge(%2, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %19
      %20 = bool.cmp lt(%5, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %20
      %21 = bool.cmp ge(%7, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %21
      %22 = bool.cmp lt(%10, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %22
      %23 = bool.cmp ge(%12, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %23
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_0 : !felt.type<"f">
    struct.member @adv_0_2 : !felt.type<"f">
    struct.member @adv_0_3 : !felt.type<"f">
    struct.member @adv_1_2 : !felt.type<"f">
    struct.member @adv_0_4 : !felt.type<"f">
    struct.member @adv_0_5 : !felt.type<"f">
    struct.member @adv_1_4 : !felt.type<"f">
  }
}
