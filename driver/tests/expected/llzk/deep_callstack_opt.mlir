module attributes { llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>> } {
  struct.def @"test group" {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">) -> !struct.type<@"test group"<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@"test group"<[]>>
      function.return %self : !struct.type<@"test group"<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@"test group"<[]>>, %arg1: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_1] : <@"test group"<[]>>, !felt.type<"bn254">
      %1 = felt.neg %0 : !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_1_1] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = felt.mul %0, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %3, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %arg1, %0 : !felt.type<"bn254">, !felt.type<"bn254">
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
      %0 = struct.readm %arg0[@adv_0_3] : <@"test group1"<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_3] : <@"test group1"<[]>>, !felt.type<"bn254">
      %2 = felt.mul %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@out_0] : <@"test group1"<[]>>, !felt.type<"bn254">
      constrain.eq %2, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %arg1, %0 : !felt.type<"bn254">, !felt.type<"bn254">
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
      %0 = struct.readm %arg0[@adv_0_4] : <@"inner group"<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_4] : <@"inner group"<[]>>, !felt.type<"bn254">
      %2 = felt.mul %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@out_0] : <@"inner group"<[]>>, !felt.type<"bn254">
      constrain.eq %2, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %arg1, %0 : !felt.type<"bn254">, !felt.type<"bn254">
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
      %2 = struct.readm %0[@out_0] : <@"inner group"<[]>>, !felt.type<"bn254">
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@adv_0_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      %4 = felt.neg %3 : !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_1_5] : <@"outer group"<[]>>, !felt.type<"bn254">
      constrain.eq %4, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = felt.mul %3, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %7 = struct.readm %arg0[@out_0] : <@"outer group"<[]>>, !felt.type<"bn254">
      constrain.eq %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
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
      %3 = struct.readm %1[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %2, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@"test group_1"] : <@Main<[]>>, !struct.type<@"test group"<[]>>
      function.call @"test group"::@constrain(%4, %2) : (!struct.type<@"test group"<[]>>, !felt.type<"bn254">) -> ()
      %5 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      %6 = struct.readm %4[@out_0] : <@"test group"<[]>>, !felt.type<"bn254">
      constrain.eq %5, %6 : !felt.type<"bn254">, !felt.type<"bn254">
      %7 = struct.readm %arg0[@"test group1_2"] : <@Main<[]>>, !struct.type<@"test group1"<[]>>
      function.call @"test group1"::@constrain(%7, %5) : (!struct.type<@"test group1"<[]>>, !felt.type<"bn254">) -> ()
      %8 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      %9 = struct.readm %7[@out_0] : <@"test group1"<[]>>, !felt.type<"bn254">
      constrain.eq %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@"outer group_3"] : <@Main<[]>>, !struct.type<@"outer group"<[]>>
      function.call @"outer group"::@constrain(%10, %8) : (!struct.type<@"outer group"<[]>>, !felt.type<"bn254">) -> ()
      %11 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      %12 = struct.readm %10[@out_0] : <@"outer group"<[]>>, !felt.type<"bn254">
      constrain.eq %11, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %11, %13 : !felt.type<"bn254">, !felt.type<"bn254">
      %14 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %13, %14 : !felt.type<"bn254">, !felt.type<"bn254">
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
