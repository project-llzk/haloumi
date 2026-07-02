module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">) -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>, %arg1: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"f">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"f">
      %0 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"f">
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type<"f">, !felt.type<"f">
      %2 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"f">
      %3 = felt.neg %2 : !felt.type<"f">
      %4 = felt.add %1, %3 : !felt.type<"f">, !felt.type<"f">
      %5 = felt.mul %felt_const_1, %4 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %5, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_0 = felt.const  1 <"f">
      %6 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"f">
      %7 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"f">
      %8 = felt.mul %6, %7 : !felt.type<"f">, !felt.type<"f">
      %9 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      %10 = felt.neg %9 : !felt.type<"f">
      %11 = felt.add %8, %10 : !felt.type<"f">, !felt.type<"f">
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_1 = felt.const  0 <"f">
      constrain.eq %12, %felt_const_0_1 : !felt.type<"f">, !felt.type<"f">
      %13 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %arg1, %13 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_1 : !felt.type<"f">
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%1, %0) : (!struct.type<@"test group"<[]>>, !felt.type<"f">) -> ()
      %2 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %3 = struct.readm %arg0[@"test group_0"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %4 = struct.readm %3[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %2, %4 : !felt.type<"f">, !felt.type<"f">
      %5 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %6 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%6, %5) : (!struct.type<@"test group"<[]>>, !felt.type<"f">) -> ()
      %7 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %8 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      %9 = struct.readm %8[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %7, %9 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %10, %arg1 : !felt.type<"f">, !felt.type<"f">
      %11 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %12 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %11, %12 : !felt.type<"f">, !felt.type<"f">
      %13 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %14 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %13, %14 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type<"f">
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type<"f">
    struct.member @adv_2_3 : !felt.type<"f">
  }
}
