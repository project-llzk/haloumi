module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type, !felt.type
      %2 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %3 = felt.neg %2 : !felt.type
      %4 = felt.add %1, %3 : !felt.type, !felt.type
      %5 = felt.mul %felt_const_1, %4 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %5, %felt_const_0 : !felt.type, !felt.type
      %felt_const_1_0 = felt.const  1
      %6 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %7 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %8 = felt.mul %6, %7 : !felt.type, !felt.type
      %9 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      %10 = felt.neg %9 : !felt.type
      %11 = felt.add %8, %10 : !felt.type, !felt.type
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type, !felt.type
      %felt_const_0_1 = felt.const  0
      constrain.eq %12, %felt_const_0_1 : !felt.type, !felt.type
      %felt_const_1_2 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %felt_const_2 = felt.const  2
      %13 = felt.neg %felt_const_2 : !felt.type
      %14 = felt.add %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3, %13 : !felt.type, !felt.type
      %felt_const_3 = felt.const  3
      %15 = felt.add %14, %felt_const_3 : !felt.type, !felt.type
      %16 = felt.mul %felt_const_1_2, %15 : !felt.type, !felt.type
      %felt_const_0_4 = felt.const  0
      constrain.eq %16, %felt_const_0_4 : !felt.type, !felt.type
      %felt_const_2_5 = felt.const  2
      %17 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type
      constrain.eq %felt_const_2_5, %17 : !felt.type, !felt.type
      %18 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %18, %arg1 : !felt.type, !felt.type
      %19 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      %20 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %19, %20 : !felt.type, !felt.type
      %felt_const_2_6 = felt.const  2
      %felt_const_2_7 = felt.const  2
      constrain.eq %felt_const_2_6, %felt_const_2_7 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @adv_1_0 : !felt.type
    struct.member @adv_2_0 : !felt.type
    struct.member @adv_3_0 : !felt.type
  }
}
