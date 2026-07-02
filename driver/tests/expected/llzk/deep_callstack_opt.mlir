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
  struct.def @"inner group" {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">) -> !struct.type<@"inner group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"inner group"<[]>>
      function.return %self : !struct.type<@"inner group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"inner group"<[]>>, %arg1: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_4] : <@"inner group"<[]>>, !felt.type<"f">
      %2 = felt.mul %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@out_0] : <@"inner group"<[]>>, !felt.type<"f">
      constrain.eq %2, %3 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %arg1, %0 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_4 : !felt.type<"f">
    struct.member @adv_1_4 : !felt.type<"f">
  }
  struct.def @"outer group" {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">) -> !struct.type<@"outer group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"outer group"<[]>>
      function.return %self : !struct.type<@"outer group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"outer group"<[]>>, %arg1: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@"inner group_0"] : <@"outer group"<[]>>, !struct.type<@"inner group"<[]>>
      function.call @"inner group"::@constrain(%0, %arg1) : (!struct.type<@"inner group"<[]>>, !felt.type<"f">) -> ()
      %1 = struct.readm %arg0[@adv_2_4] : <@"outer group"<[]>>, !felt.type<"f">
      %2 = struct.readm %0[@out_0] : <@"inner group"<[]>>, !felt.type<"f">
      constrain.eq %1, %2 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type<"f">
      %4 = felt.neg %3 : !felt.type<"f">
      %5 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type<"f">
      constrain.eq %4, %5 : !felt.type<"f">, !felt.type<"f">
      %6 = felt.mul %3, %5 : !felt.type<"f">, !felt.type<"f">
      %7 = struct.readm %arg0[@out_0] : <@"outer group"<[]>>, !felt.type<"f">
      constrain.eq %6, %7 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %1, %3 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @"inner group_0" : !struct.type<@"inner group"<[]>>
    struct.member @adv_2_4 : !felt.type<"f">
    struct.member @adv_0_5 : !felt.type<"f">
    struct.member @adv_1_5 : !felt.type<"f">
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
      %10 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      function.call @"outer group"::@constrain(%10, %8) : (!struct.type<@"outer group"<[]>>, !felt.type<"f">) -> ()
      %11 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %12 = struct.readm %10[@out_0] : <@"outer group"<[]>>, !felt.type<"f">
      constrain.eq %11, %12 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %0, %arg1 : !felt.type<"f">, !felt.type<"f">
      %13 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %11, %13 : !felt.type<"f">, !felt.type<"f">
      %14 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %13, %14 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @"test group_0" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_1 : !felt.type<"f">
    struct.member @"test group_1" : !struct.type<@"test group"<[]>>
    struct.member @adv_2_2 : !felt.type<"f">
    struct.member @"test group1_2" : !struct.type<@"test group1"<[]>>
    struct.member @adv_2_3 : !felt.type<"f">
    struct.member @"outer group_3" : !struct.type<@"outer group"<[]>>
    struct.member @adv_2_5 : !felt.type<"f">
    struct.member @adv_2_6 : !felt.type<"f">
  }
}
