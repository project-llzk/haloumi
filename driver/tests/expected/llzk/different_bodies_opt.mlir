module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">) -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>, %arg1: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"f">
      %1 = felt.neg %0 : !felt.type<"f">
      %2 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %1, %2 : !felt.type<"f">, !felt.type<"f">
      %3 = felt.mul %0, %2 : !felt.type<"f">, !felt.type<"f">
      %4 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %3, %4 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %arg1, %0 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_1 : !felt.type<"f">
  }
  struct.def @"test group1" {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">) -> !struct.type<@"test group1"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group1"<[]>>
      function.return %self : !struct.type<@"test group1"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group1"<[]>>, %arg1: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_3] : <@"test group1"<[]>>, !felt.type<"f">
      %2 = felt.mul %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@out_0] : <@"test group1"<[]>>, !felt.type<"f">
      constrain.eq %2, %3 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %arg1, %0 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_3 : !felt.type<"f">
    struct.member @adv_1_3 : !felt.type<"f">
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
      %3 = struct.readm %1[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %2, %3 : !felt.type<"f">, !felt.type<"f">
      %4 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%4, %2) : (!struct.type<@"test group"<[]>>, !felt.type<"f">) -> ()
      %5 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %6 = struct.readm %4[@out_0] : <@"test group"<[]>>, !felt.type<"f">
      constrain.eq %5, %6 : !felt.type<"f">, !felt.type<"f">
      %7 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      function.call @"test group1"::@constrain(%7, %5) : (!struct.type<@"test group1"<[]>>, !felt.type<"f">) -> ()
      %8 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %9 = struct.readm %7[@out_0] : <@"test group1"<[]>>, !felt.type<"f">
      constrain.eq %8, %9 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %0, %arg1 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %8, %10 : !felt.type<"f">, !felt.type<"f">
      %11 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %10, %11 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type<"f">
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type<"f">
    struct.member @"test group1_2" : !struct.type<@"test group1"<[]>>
    struct.member @adv_2_3 : !felt.type<"f">
    struct.member @adv_2_4 : !felt.type<"f">
  }
}
