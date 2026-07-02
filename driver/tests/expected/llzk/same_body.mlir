module attributes {llzk.lang = "haloumi"} {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type) -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>, %arg1: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %0 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type, !felt.type
      %2 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type
      %3 = felt.neg %2 : !felt.type
      %4 = felt.add %1, %3 : !felt.type, !felt.type
      %5 = felt.mul %felt_const_1, %4 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %5, %felt_const_0 : !felt.type, !felt.type
      %felt_const_1_0 = felt.const  1
      %6 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type
      %7 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type
      %8 = felt.mul %6, %7 : !felt.type, !felt.type
      %9 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type
      %10 = felt.neg %9 : !felt.type
      %11 = felt.add %8, %10 : !felt.type, !felt.type
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type, !felt.type
      %felt_const_0_1 = felt.const  0
      constrain.eq %12, %felt_const_0_1 : !felt.type, !felt.type
      %13 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type
      constrain.eq %arg1, %13 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_1 : !felt.type
    struct.member @adv_1_1 : !felt.type
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%1, %0) : (!struct.type<@"test group"<[]>>, !felt.type) -> ()
      %2 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      %3 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %4 = struct.readm %3[@out_0] : <@"test group"<[]>>, !felt.type
      constrain.eq %2, %4 : !felt.type, !felt.type
      %5 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      %6 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%6, %5) : (!struct.type<@"test group"<[]>>, !felt.type) -> ()
      %7 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      %8 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %9 = struct.readm %8[@out_0] : <@"test group"<[]>>, !felt.type
      constrain.eq %7, %9 : !felt.type, !felt.type
      %10 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %10, %arg1 : !felt.type, !felt.type
      %11 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      %12 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      constrain.eq %11, %12 : !felt.type, !felt.type
      %13 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      %14 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %13, %14 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type
    struct.member @adv_2_3 : !felt.type
  }
}
