module attributes { llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>> } {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      %2 = felt.add %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %2, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"bn254">
      %6 = felt.add %4, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %8 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      %10 = felt.add %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %11 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %10, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %12 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %13 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"bn254">
      %14 = felt.add %12, %13 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %14, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %16 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %17 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      %18 = felt.add %16, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %19 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %18, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      %20 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %21 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"bn254">
      %22 = felt.add %20, %21 : !felt.type<"bn254">, !felt.type<"bn254">
      %23 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %22, %23 : !felt.type<"bn254">, !felt.type<"bn254">
      %24 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"bn254">
      %25 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"bn254">
      %26 = felt.add %24, %25 : !felt.type<"bn254">, !felt.type<"bn254">
      %27 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %26, %27 : !felt.type<"bn254">, !felt.type<"bn254">
      %28 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"bn254">
      %29 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"bn254">
      %30 = felt.add %28, %29 : !felt.type<"bn254">, !felt.type<"bn254">
      %31 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %30, %31 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %4, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %8, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %12, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %16, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %20, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %24, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %28, %23 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %1, %arg2 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %5, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %9, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %13, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %17, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %21, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %25, %23 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %29, %27 : !felt.type<"bn254">, !felt.type<"bn254">
      %32 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %31, %32 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254">
    struct.member @adv_1_0 : !felt.type<"bn254">
    struct.member @adv_2_0 : !felt.type<"bn254">
    struct.member @adv_0_1 : !felt.type<"bn254">
    struct.member @adv_1_1 : !felt.type<"bn254">
    struct.member @adv_2_1 : !felt.type<"bn254">
    struct.member @adv_0_2 : !felt.type<"bn254">
    struct.member @adv_1_2 : !felt.type<"bn254">
    struct.member @adv_2_2 : !felt.type<"bn254">
    struct.member @adv_0_3 : !felt.type<"bn254">
    struct.member @adv_1_3 : !felt.type<"bn254">
    struct.member @adv_2_3 : !felt.type<"bn254">
    struct.member @adv_0_4 : !felt.type<"bn254">
    struct.member @adv_1_4 : !felt.type<"bn254">
    struct.member @adv_2_4 : !felt.type<"bn254">
    struct.member @adv_0_5 : !felt.type<"bn254">
    struct.member @adv_1_5 : !felt.type<"bn254">
    struct.member @adv_2_5 : !felt.type<"bn254">
    struct.member @adv_0_6 : !felt.type<"bn254">
    struct.member @adv_1_6 : !felt.type<"bn254">
    struct.member @adv_2_6 : !felt.type<"bn254">
    struct.member @adv_0_7 : !felt.type<"bn254">
    struct.member @adv_1_7 : !felt.type<"bn254">
    struct.member @adv_2_7 : !felt.type<"bn254">
  }
}
