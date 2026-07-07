module attributes { llzk.lang = "halo2"} {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">) -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>, %arg1: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %0 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"bn254">
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type<"bn254">, !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"bn254">
      %3 = felt.neg %2 : !felt.type<"bn254">
      %4 = felt.add %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = felt.mul %felt_const_1, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %5, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_0 = felt.const  1 <"bn254">
      %6 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"bn254">
      %8 = felt.mul %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %10 = felt.neg %9 : !felt.type<"bn254">
      %11 = felt.add %8, %10 : !felt.type<"bn254">, !felt.type<"bn254">
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_1 = felt.const  0 <"bn254">
      constrain.eq %12, %felt_const_0_1 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %arg1, %13 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_1 : !felt.type<"bn254">
    struct.member @adv_1_1 : !felt.type<"bn254">
  }
  struct.def @"test group1" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">) -> !struct.type<@"test group1"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group1"<[]>>
      function.return %self : !struct.type<@"test group1"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group1"<[]>>, %arg1: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %0 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_3] : <@"test group1"<[]>>, !felt.type<"bn254">
      %2 = felt.mul %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@out_0] : <@"test group1"<[]>>, !felt.type<"bn254">
      %4 = felt.neg %3 : !felt.type<"bn254">
      %5 = felt.add %2, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %6, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type<"bn254">
      constrain.eq %arg1, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_3 : !felt.type<"bn254">
    struct.member @adv_1_3 : !felt.type<"bn254">
  }
  struct.def @"inner group" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">) -> !struct.type<@"inner group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"inner group"<[]>>
      function.return %self : !struct.type<@"inner group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"inner group"<[]>>, %arg1: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %0 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_4] : <@"inner group"<[]>>, !felt.type<"bn254">
      %2 = felt.mul %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@out_0] : <@"inner group"<[]>>, !felt.type<"bn254">
      %4 = felt.neg %3 : !felt.type<"bn254">
      %5 = felt.add %2, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %6, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type<"bn254">
      constrain.eq %arg1, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_4 : !felt.type<"bn254">
    struct.member @adv_1_4 : !felt.type<"bn254">
  }
  struct.def @"outer group" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">) -> !struct.type<@"outer group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"outer group"<[]>>
      function.return %self : !struct.type<@"outer group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"outer group"<[]>>, %arg1: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@"inner group_0"] : <@"outer group"<[]>>, !struct.type<@"inner group"<[]>>
      function.call @"inner group"::@constrain(%0, %arg1) : (!struct.type<@"inner group"<[]>>, !felt.type<"bn254">) -> ()
      %1 = struct.readm %arg0[@adv_2_4] : <@"outer group"<[]>>, !felt.type<"bn254">
      %2 = struct.readm %arg0[@"inner group_0"] : <@"outer group"<[]>>, !struct.type<@"inner group"<[]>>
      %3 = struct.readm %2[@out_0] : <@"inner group"<[]>>, !felt.type<"bn254">
      constrain.eq %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %4 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      %5 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      %7 = felt.neg %6 : !felt.type<"bn254">
      %8 = felt.add %5, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = felt.mul %felt_const_1, %8 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %9, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_0 = felt.const  1 <"bn254">
      %10 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      %11 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      %12 = felt.mul %10, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = struct.readm %arg0[@out_0] : <@"outer group"<[]>>, !felt.type<"bn254">
      %14 = felt.neg %13 : !felt.type<"bn254">
      %15 = felt.add %12, %14 : !felt.type<"bn254">, !felt.type<"bn254">
      %16 = felt.mul %felt_const_1_0, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_1 = felt.const  0 <"bn254">
      constrain.eq %16, %felt_const_0_1 : !felt.type<"bn254">, !felt.type<"bn254">
      %17 = struct.readm %arg0[@adv_2_4] : <@"outer group"<[]>>, !felt.type<"bn254">
      %18 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      constrain.eq %17, %18 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @"inner group_0" : !struct.type<@"inner group"<[]>>
    struct.member @adv_2_4 : !felt.type<"bn254">
    struct.member @adv_0_5 : !felt.type<"bn254">
    struct.member @adv_1_5 : !felt.type<"bn254">
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%1, %0) : (!struct.type<@"test group"<[]>>, !felt.type<"bn254">) -> ()
      %2 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      %3 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %4 = struct.readm %3[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %2, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      %6 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%6, %5) : (!struct.type<@"test group"<[]>>, !felt.type<"bn254">) -> ()
      %7 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      %8 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %9 = struct.readm %8[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %7, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      %11 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      function.call @"test group1"::@constrain(%11, %10) : (!struct.type<@"test group1"<[]>>, !felt.type<"bn254">) -> ()
      %12 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      %13 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      %14 = struct.readm %13[@out_0] : <@"test group1"<[]>>, !felt.type<"bn254">
      constrain.eq %12, %14 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      %16 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      function.call @"outer group"::@constrain(%16, %15) : (!struct.type<@"outer group"<[]>>, !felt.type<"bn254">) -> ()
      %17 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      %18 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      %19 = struct.readm %18[@out_0] : <@"outer group"<[]>>, !felt.type<"bn254">
      constrain.eq %17, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      %20 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %20, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %21 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      %22 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %21, %22 : !felt.type<"bn254">, !felt.type<"bn254">
      %23 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      %24 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %23, %24 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254">
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type<"bn254">
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type<"bn254">
    struct.member @"test group1_2" : !struct.type<@"test group1"<[]>>
    struct.member @adv_2_3 : !felt.type<"bn254">
    struct.member @"outer group_3" : !struct.type<@"outer group"<[]>>
    struct.member @adv_2_5 : !felt.type<"bn254">
    struct.member @adv_2_6 : !felt.type<"bn254">
  }
}
