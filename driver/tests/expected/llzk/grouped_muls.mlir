module attributes { llzk.lang = "halo2"} {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute() -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %0 = struct.readm %arg0[@adv_0_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type<"bn254">, !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_1_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %3 = felt.neg %2 : !felt.type<"bn254">
      %4 = felt.add %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = felt.mul %felt_const_1, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %5, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_0 = felt.const  1 <"bn254">
      %6 = struct.readm %arg0[@adv_0_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_1_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %8 = felt.mul %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      %10 = felt.neg %9 : !felt.type<"bn254">
      %11 = felt.add %8, %10 : !felt.type<"bn254">, !felt.type<"bn254">
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_1 = felt.const  0 <"bn254">
      constrain.eq %12, %felt_const_0_1 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254">
    struct.member @adv_1_0 : !felt.type<"bn254">
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%0) : (!struct.type<@"test group"<[]>>) -> ()
      %1 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      %2 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %3 = struct.readm %2[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      %5 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %4, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_0 : !felt.type<"bn254">
  }
}
