module attributes {llzk.lang = "haloumi"} {
  struct.def @mul_many {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type, %arg1: !felt.type) -> !struct.type<@mul_many<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@mul_many<[]>>
      function.return %self : !struct.type<@mul_many<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@mul_many<[]>>, %arg1: !felt.type, %arg2: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %0 = struct.readm %arg0[@adv_0_4] : <@mul_many<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_1_4] : <@mul_many<[]>>, !felt.type
      %2 = felt.mul %0, %1 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@out_0] : <@mul_many<[]>>, !felt.type
      %4 = felt.neg %3 : !felt.type
      %5 = felt.add %2, %4 : !felt.type, !felt.type
      %6 = felt.mul %felt_const_1, %5 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %6, %felt_const_0 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@adv_0_4] : <@mul_many<[]>>, !felt.type
      constrain.eq %arg1, %7 : !felt.type, !felt.type
      %8 = struct.readm %arg0[@adv_1_4] : <@mul_many<[]>>, !felt.type
      constrain.eq %arg2, %8 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_4 : !felt.type
    struct.member @adv_1_4 : !felt.type
  }
  struct.def @mul_many1 {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type, %arg1: !felt.type, %arg2: !felt.type) -> !struct.type<@mul_many1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@mul_many1<[]>>
      function.return %self : !struct.type<@mul_many1<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@mul_many1<[]>>, %arg1: !felt.type, %arg2: !felt.type, %arg3: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@mul_many_0] : <@mul_many1<[]>>, !struct.type<@mul_many<[]>>
      function.call @mul_many::@constrain(%0, %arg2, %arg3) : (!struct.type<@mul_many<[]>>, !felt.type, !felt.type) -> ()
      %1 = struct.readm %arg0[@adv_2_4] : <@mul_many1<[]>>, !felt.type
      %2 = struct.readm %arg0[@mul_many_0] : <@mul_many1<[]>>, !struct.type<@mul_many<[]>>
      %3 = struct.readm %2[@out_0] : <@mul_many<[]>>, !felt.type
      constrain.eq %1, %3 : !felt.type, !felt.type
      %felt_const_1 = felt.const  1
      %4 = struct.readm %arg0[@adv_0_5] : <@mul_many1<[]>>, !felt.type
      %5 = struct.readm %arg0[@adv_1_5] : <@mul_many1<[]>>, !felt.type
      %6 = felt.mul %4, %5 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@out_0] : <@mul_many1<[]>>, !felt.type
      %8 = felt.neg %7 : !felt.type
      %9 = felt.add %6, %8 : !felt.type, !felt.type
      %10 = felt.mul %felt_const_1, %9 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %10, %felt_const_0 : !felt.type, !felt.type
      %11 = struct.readm %arg0[@adv_0_5] : <@mul_many1<[]>>, !felt.type
      constrain.eq %arg1, %11 : !felt.type, !felt.type
      %12 = struct.readm %arg0[@adv_2_4] : <@mul_many1<[]>>, !felt.type
      %13 = struct.readm %arg0[@adv_1_5] : <@mul_many1<[]>>, !felt.type
      constrain.eq %12, %13 : !felt.type, !felt.type
      function.return
    }
    struct.member @mul_many_0 : !struct.type<@mul_many<[]>>
    struct.member @adv_2_4 : !felt.type
    struct.member @adv_0_5 : !felt.type
    struct.member @adv_1_5 : !felt.type
  }
  struct.def @mul_many2 {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type, %arg1: !felt.type, %arg2: !felt.type, %arg3: !felt.type) -> !struct.type<@mul_many2<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@mul_many2<[]>>
      function.return %self : !struct.type<@mul_many2<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@mul_many2<[]>>, %arg1: !felt.type, %arg2: !felt.type, %arg3: !felt.type, %arg4: !felt.type) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@mul_many1_0] : <@mul_many2<[]>>, !struct.type<@mul_many1<[]>>
      function.call @mul_many1::@constrain(%0, %arg2, %arg3, %arg4) : (!struct.type<@mul_many1<[]>>, !felt.type, !felt.type, !felt.type) -> ()
      %1 = struct.readm %arg0[@adv_2_5] : <@mul_many2<[]>>, !felt.type
      %2 = struct.readm %arg0[@mul_many1_0] : <@mul_many2<[]>>, !struct.type<@mul_many1<[]>>
      %3 = struct.readm %2[@out_0] : <@mul_many1<[]>>, !felt.type
      constrain.eq %1, %3 : !felt.type, !felt.type
      %felt_const_1 = felt.const  1
      %4 = struct.readm %arg0[@adv_0_6] : <@mul_many2<[]>>, !felt.type
      %5 = struct.readm %arg0[@adv_1_6] : <@mul_many2<[]>>, !felt.type
      %6 = felt.mul %4, %5 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@out_0] : <@mul_many2<[]>>, !felt.type
      %8 = felt.neg %7 : !felt.type
      %9 = felt.add %6, %8 : !felt.type, !felt.type
      %10 = felt.mul %felt_const_1, %9 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %10, %felt_const_0 : !felt.type, !felt.type
      %11 = struct.readm %arg0[@adv_0_6] : <@mul_many2<[]>>, !felt.type
      constrain.eq %arg1, %11 : !felt.type, !felt.type
      %12 = struct.readm %arg0[@adv_2_5] : <@mul_many2<[]>>, !felt.type
      %13 = struct.readm %arg0[@adv_1_6] : <@mul_many2<[]>>, !felt.type
      constrain.eq %12, %13 : !felt.type, !felt.type
      function.return
    }
    struct.member @mul_many1_0 : !struct.type<@mul_many1<[]>>
    struct.member @adv_2_5 : !felt.type
    struct.member @adv_0_6 : !felt.type
    struct.member @adv_1_6 : !felt.type
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}, %arg3: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}, %arg3: !felt.type {llzk.pub = #llzk.pub}, %arg4: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %2 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %3 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %4 = struct.readm %arg0[@mul_many2_0] : <@Main<[]>>, !struct.type<@mul_many2<[]>>
      function.call @mul_many2::@constrain(%4, %0, %1, %2, %3) : (!struct.type<@mul_many2<[]>>, !felt.type, !felt.type, !felt.type, !felt.type) -> ()
      %5 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      %6 = struct.readm %arg0[@mul_many2_0] : <@Main<[]>>, !struct.type<@mul_many2<[]>>
      %7 = struct.readm %6[@out_0] : <@mul_many2<[]>>, !felt.type
      constrain.eq %5, %7 : !felt.type, !felt.type
      %8 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %8, %arg1 : !felt.type, !felt.type
      %9 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      constrain.eq %9, %arg2 : !felt.type, !felt.type
      %10 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      constrain.eq %10, %arg3 : !felt.type, !felt.type
      %11 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      constrain.eq %11, %arg4 : !felt.type, !felt.type
      %12 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      %13 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %12, %13 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @adv_0_1 : !felt.type
    struct.member @adv_0_2 : !felt.type
    struct.member @adv_0_3 : !felt.type
    struct.member @mul_many2_0 : !struct.type<@mul_many2<[]>>
    struct.member @adv_2_6 : !felt.type
  }
}
