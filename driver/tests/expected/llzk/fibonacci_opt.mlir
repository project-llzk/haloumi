module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}, %arg1: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %2 = felt.add %0, %1 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      constrain.eq %2, %3 : !felt.type, !felt.type
      %4 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %5 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type
      %6 = felt.add %4, %5 : !felt.type, !felt.type
      %7 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      constrain.eq %6, %7 : !felt.type, !felt.type
      %8 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type
      %10 = felt.add %8, %9 : !felt.type, !felt.type
      %11 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      constrain.eq %10, %11 : !felt.type, !felt.type
      %12 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %13 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type
      %14 = felt.add %12, %13 : !felt.type, !felt.type
      %15 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      constrain.eq %14, %15 : !felt.type, !felt.type
      %16 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %17 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type
      %18 = felt.add %16, %17 : !felt.type, !felt.type
      %19 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type
      constrain.eq %18, %19 : !felt.type, !felt.type
      %20 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %21 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type
      %22 = felt.add %20, %21 : !felt.type, !felt.type
      %23 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      constrain.eq %22, %23 : !felt.type, !felt.type
      %24 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type
      %25 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type
      %26 = felt.add %24, %25 : !felt.type, !felt.type
      %27 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      constrain.eq %26, %27 : !felt.type, !felt.type
      %28 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type
      %29 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type
      %30 = felt.add %28, %29 : !felt.type, !felt.type
      %31 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type
      constrain.eq %30, %31 : !felt.type, !felt.type
      constrain.eq %0, %arg1 : !felt.type, !felt.type
      constrain.eq %4, %1 : !felt.type, !felt.type
      constrain.eq %8, %3 : !felt.type, !felt.type
      constrain.eq %12, %7 : !felt.type, !felt.type
      constrain.eq %16, %11 : !felt.type, !felt.type
      constrain.eq %20, %15 : !felt.type, !felt.type
      constrain.eq %24, %19 : !felt.type, !felt.type
      constrain.eq %28, %23 : !felt.type, !felt.type
      constrain.eq %1, %arg2 : !felt.type, !felt.type
      constrain.eq %5, %3 : !felt.type, !felt.type
      constrain.eq %9, %7 : !felt.type, !felt.type
      constrain.eq %13, %11 : !felt.type, !felt.type
      constrain.eq %17, %15 : !felt.type, !felt.type
      constrain.eq %21, %19 : !felt.type, !felt.type
      constrain.eq %25, %23 : !felt.type, !felt.type
      constrain.eq %29, %27 : !felt.type, !felt.type
      %32 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %31, %32 : !felt.type, !felt.type
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @adv_1_0 : !felt.type
    struct.member @adv_2_0 : !felt.type
    struct.member @adv_0_1 : !felt.type
    struct.member @adv_1_1 : !felt.type
    struct.member @adv_2_1 : !felt.type
    struct.member @adv_0_2 : !felt.type
    struct.member @adv_1_2 : !felt.type
    struct.member @adv_2_2 : !felt.type
    struct.member @adv_0_3 : !felt.type
    struct.member @adv_1_3 : !felt.type
    struct.member @adv_2_3 : !felt.type
    struct.member @adv_0_4 : !felt.type
    struct.member @adv_1_4 : !felt.type
    struct.member @adv_2_4 : !felt.type
    struct.member @adv_0_5 : !felt.type
    struct.member @adv_1_5 : !felt.type
    struct.member @adv_2_5 : !felt.type
    struct.member @adv_0_6 : !felt.type
    struct.member @adv_1_6 : !felt.type
    struct.member @adv_2_6 : !felt.type
    struct.member @adv_0_7 : !felt.type
    struct.member @adv_1_7 : !felt.type
    struct.member @adv_2_7 : !felt.type
  }
}
