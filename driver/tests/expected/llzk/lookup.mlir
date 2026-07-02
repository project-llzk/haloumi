module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"f">
      %0 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %2 = felt.mul %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      %4 = felt.neg %3 : !felt.type<"f">
      %5 = felt.add %2, %4 : !felt.type<"f">, !felt.type<"f">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %6, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_0 = felt.const  1 <"f">
      %7 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %8 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      %9 = felt.mul %7, %8 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"f">
      %11 = felt.neg %10 : !felt.type<"f">
      %12 = felt.add %9, %11 : !felt.type<"f">, !felt.type<"f">
      %13 = felt.mul %felt_const_1_0, %12 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_1 = felt.const  0 <"f">
      constrain.eq %13, %felt_const_0_1 : !felt.type<"f">, !felt.type<"f">
      %14 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %14, %arg1 : !felt.type<"f">, !felt.type<"f">
      %15 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"f">
      %16 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %15, %16 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_1_0 : !felt.type<"f">
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @adv_2_0 : !felt.type<"f">
    struct.member @adv_3_0 : !felt.type<"f">
  }
}
