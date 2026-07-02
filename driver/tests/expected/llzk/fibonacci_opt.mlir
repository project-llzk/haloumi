module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %2 = felt.add %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %2, %3 : !felt.type<"f">, !felt.type<"f">
      %4 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %5 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"f">
      %6 = felt.add %4, %5 : !felt.type<"f">, !felt.type<"f">
      %7 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %6, %7 : !felt.type<"f">, !felt.type<"f">
      %8 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      %10 = felt.add %8, %9 : !felt.type<"f">, !felt.type<"f">
      %11 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %10, %11 : !felt.type<"f">, !felt.type<"f">
      %12 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %13 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"f">
      %14 = felt.add %12, %13 : !felt.type<"f">, !felt.type<"f">
      %15 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %14, %15 : !felt.type<"f">, !felt.type<"f">
      %16 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %17 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      %18 = felt.add %16, %17 : !felt.type<"f">, !felt.type<"f">
      %19 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %18, %19 : !felt.type<"f">, !felt.type<"f">
      %20 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %21 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"f">
      %22 = felt.add %20, %21 : !felt.type<"f">, !felt.type<"f">
      %23 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %22, %23 : !felt.type<"f">, !felt.type<"f">
      %24 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"f">
      %25 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"f">
      %26 = felt.add %24, %25 : !felt.type<"f">, !felt.type<"f">
      %27 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %26, %27 : !felt.type<"f">, !felt.type<"f">
      %28 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"f">
      %29 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"f">
      %30 = felt.add %28, %29 : !felt.type<"f">, !felt.type<"f">
      %31 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %30, %31 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %0, %arg1 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %4, %1 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %8, %3 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %12, %7 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %16, %11 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %20, %15 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %24, %19 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %28, %23 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %1, %arg2 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %5, %3 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %9, %7 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %13, %11 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %17, %15 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %21, %19 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %25, %23 : !felt.type<"f">, !felt.type<"f">
      constrain.eq %29, %27 : !felt.type<"f">, !felt.type<"f">
      %32 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %31, %32 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @adv_1_0 : !felt.type<"f">
    struct.member @adv_2_0 : !felt.type<"f">
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_1 : !felt.type<"f">
    struct.member @adv_2_1 : !felt.type<"f">
    struct.member @adv_0_2 : !felt.type<"f">
    struct.member @adv_1_2 : !felt.type<"f">
    struct.member @adv_2_2 : !felt.type<"f">
    struct.member @adv_0_3 : !felt.type<"f">
    struct.member @adv_1_3 : !felt.type<"f">
    struct.member @adv_2_3 : !felt.type<"f">
    struct.member @adv_0_4 : !felt.type<"f">
    struct.member @adv_1_4 : !felt.type<"f">
    struct.member @adv_2_4 : !felt.type<"f">
    struct.member @adv_0_5 : !felt.type<"f">
    struct.member @adv_1_5 : !felt.type<"f">
    struct.member @adv_2_5 : !felt.type<"f">
    struct.member @adv_0_6 : !felt.type<"f">
    struct.member @adv_1_6 : !felt.type<"f">
    struct.member @adv_2_6 : !felt.type<"f">
    struct.member @adv_0_7 : !felt.type<"f">
    struct.member @adv_1_7 : !felt.type<"f">
    struct.member @adv_2_7 : !felt.type<"f">
  }
}
