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
  struct.def @"test group1" {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type) -> !struct.type<@"test group1"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group1"<[]>>
      function.return %self : !struct.type<@"test group1"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group1"<[]>>, %arg1: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %0 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_1_3] : <@"test group1"<[]>>, !felt.type
      %2 = felt.mul %0, %1 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@out_0] : <@"test group1"<[]>>, !felt.type
      %4 = felt.neg %3 : !felt.type
      %5 = felt.add %2, %4 : !felt.type, !felt.type
      %6 = felt.mul %felt_const_1, %5 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %6, %felt_const_0 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type
      constrain.eq %arg1, %7 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_3 : !felt.type
    struct.member @adv_1_3 : !felt.type
  }
  struct.def @"inner group" {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type) -> !struct.type<@"inner group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"inner group"<[]>>
      function.return %self : !struct.type<@"inner group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"inner group"<[]>>, %arg1: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %0 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_1_4] : <@"inner group"<[]>>, !felt.type
      %2 = felt.mul %0, %1 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@out_0] : <@"inner group"<[]>>, !felt.type
      %4 = felt.neg %3 : !felt.type
      %5 = felt.add %2, %4 : !felt.type, !felt.type
      %6 = felt.mul %felt_const_1, %5 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %6, %felt_const_0 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type
      constrain.eq %arg1, %7 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_4 : !felt.type
    struct.member @adv_1_4 : !felt.type
  }
  struct.def @"outer group" {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type) -> !struct.type<@"outer group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"outer group"<[]>>
      function.return %self : !struct.type<@"outer group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"outer group"<[]>>, %arg1: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@"inner group_0"] : <@"outer group"<[]>>, !struct.type<@"inner group"<[]>>
      function.call @"inner group"::@constrain(%0, %arg1) : (!struct.type<@"inner group"<[]>>, !felt.type) -> ()
      %1 = struct.readm %arg0[@adv_2_4] : <@"outer group"<[]>>, !felt.type
      %2 = struct.readm %arg0[@"inner group_0"] : <@"outer group"<[]>>, !struct.type<@"inner group"<[]>>
      %3 = struct.readm %2[@out_0] : <@"inner group"<[]>>, !felt.type
      constrain.eq %1, %3 : !felt.type, !felt.type
      %felt_const_1 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %4 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type
      %5 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %4 : !felt.type, !felt.type
      %6 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type
      %7 = felt.neg %6 : !felt.type
      %8 = felt.add %5, %7 : !felt.type, !felt.type
      %9 = felt.mul %felt_const_1, %8 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %9, %felt_const_0 : !felt.type, !felt.type
      %felt_const_1_0 = felt.const  1
      %10 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type
      %11 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type
      %12 = felt.mul %10, %11 : !felt.type, !felt.type
      %13 = struct.readm %arg0[@out_0] : <@"outer group"<[]>>, !felt.type
      %14 = felt.neg %13 : !felt.type
      %15 = felt.add %12, %14 : !felt.type, !felt.type
      %16 = felt.mul %felt_const_1_0, %15 : !felt.type, !felt.type
      %felt_const_0_1 = felt.const  0
      constrain.eq %16, %felt_const_0_1 : !felt.type, !felt.type
      %17 = struct.readm %arg0[@adv_2_4] : <@"outer group"<[]>>, !felt.type
      %18 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type
      constrain.eq %17, %18 : !felt.type, !felt.type
      function.return
    }
    struct.member @"inner group_0" : !struct.type<@"inner group"<[]>>
    struct.member @adv_2_4 : !felt.type
    struct.member @adv_0_5 : !felt.type
    struct.member @adv_1_5 : !felt.type
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
      %10 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      %11 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      function.call @"test group1"::@constrain(%11, %10) : (!struct.type<@"test group1"<[]>>, !felt.type) -> ()
      %12 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      %13 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      %14 = struct.readm %13[@out_0] : <@"test group1"<[]>>, !felt.type
      constrain.eq %12, %14 : !felt.type, !felt.type
      %15 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      %16 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      function.call @"outer group"::@constrain(%16, %15) : (!struct.type<@"outer group"<[]>>, !felt.type) -> ()
      %17 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      %18 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      %19 = struct.readm %18[@out_0] : <@"outer group"<[]>>, !felt.type
      constrain.eq %17, %19 : !felt.type, !felt.type
      %20 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %20, %arg1 : !felt.type, !felt.type
      %21 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      %22 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      constrain.eq %21, %22 : !felt.type, !felt.type
      %23 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      %24 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %23, %24 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type
    struct.member @"test group1_2" : !struct.type<@"test group1"<[]>>
    struct.member @adv_2_3 : !felt.type
    struct.member @"outer group_3" : !struct.type<@"outer group"<[]>>
    struct.member @adv_2_5 : !felt.type
    struct.member @adv_2_6 : !felt.type
  }
}
