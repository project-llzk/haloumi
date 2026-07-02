module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    struct.member @out_1 : !felt.type<"f"> {llzk.pub}
    struct.member @out_2 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"f">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"f">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type<"f">, !felt.type<"f">
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %3 = felt.neg %2 : !felt.type<"f">
      %4 = felt.add %1, %3 : !felt.type<"f">, !felt.type<"f">
      %5 = felt.mul %felt_const_1, %4 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %5, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_0 = felt.const  1 <"f">
      %6 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %8 = felt.mul %6, %7 : !felt.type<"f">, !felt.type<"f">
      %9 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %10 = felt.neg %9 : !felt.type<"f">
      %11 = felt.add %8, %10 : !felt.type<"f">, !felt.type<"f">
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_1 = felt.const  0 <"f">
      constrain.eq %12, %felt_const_0_1 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_2 = felt.const  1 <"f">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"f">
      %13 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %14 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3, %13 : !felt.type<"f">, !felt.type<"f">
      %15 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %16 = felt.neg %15 : !felt.type<"f">
      %17 = felt.add %14, %16 : !felt.type<"f">, !felt.type<"f">
      %18 = felt.mul %felt_const_1_2, %17 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_4 = felt.const  0 <"f">
      constrain.eq %18, %felt_const_0_4 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_5 = felt.const  1 <"f">
      %19 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %20 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %21 = felt.mul %19, %20 : !felt.type<"f">, !felt.type<"f">
      %22 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      %23 = felt.neg %22 : !felt.type<"f">
      %24 = felt.add %21, %23 : !felt.type<"f">, !felt.type<"f">
      %25 = felt.mul %felt_const_1_5, %24 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_6 = felt.const  0 <"f">
      constrain.eq %25, %felt_const_0_6 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_7 = felt.const  1 <"f">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"f">
      %26 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %27 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8, %26 : !felt.type<"f">, !felt.type<"f">
      %28 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %29 = felt.neg %28 : !felt.type<"f">
      %30 = felt.add %27, %29 : !felt.type<"f">, !felt.type<"f">
      %31 = felt.mul %felt_const_1_7, %30 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_9 = felt.const  0 <"f">
      constrain.eq %31, %felt_const_0_9 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_10 = felt.const  1 <"f">
      %32 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %33 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %34 = felt.mul %32, %33 : !felt.type<"f">, !felt.type<"f">
      %35 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      %36 = felt.neg %35 : !felt.type<"f">
      %37 = felt.add %34, %36 : !felt.type<"f">, !felt.type<"f">
      %38 = felt.mul %felt_const_1_10, %37 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_11 = felt.const  0 <"f">
      constrain.eq %38, %felt_const_0_11 : !felt.type<"f">, !felt.type<"f">
      %39 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %39, %arg1 : !felt.type<"f">, !felt.type<"f">
      %40 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %40, %arg1 : !felt.type<"f">, !felt.type<"f">
      %41 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %41, %arg1 : !felt.type<"f">, !felt.type<"f">
      %42 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %43 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %42, %43 : !felt.type<"f">, !felt.type<"f">
      %44 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      %45 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %44, %45 : !felt.type<"f">, !felt.type<"f">
      %46 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      %47 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %46, %47 : !felt.type<"f">, !felt.type<"f">
      %48 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000 = felt.const  1000 <"f">
      %49 = bool.cmp lt(%48, %felt_const_1000) : !felt.type<"f">, !felt.type<"f">
      bool.assert %49
      %50 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000_12 = felt.const  1000 <"f">
      %51 = bool.cmp ge(%50, %felt_const_1000_12) : !felt.type<"f">, !felt.type<"f">
      bool.assert %51
      %52 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000_13 = felt.const  1000 <"f">
      %53 = bool.cmp lt(%52, %felt_const_1000_13) : !felt.type<"f">, !felt.type<"f">
      bool.assert %53
      %54 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000_14 = felt.const  1000 <"f">
      %55 = bool.cmp ge(%54, %felt_const_1000_14) : !felt.type<"f">, !felt.type<"f">
      bool.assert %55
      %56 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000_15 = felt.const  1000 <"f">
      %57 = bool.cmp lt(%56, %felt_const_1000_15) : !felt.type<"f">, !felt.type<"f">
      bool.assert %57
      %58 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %felt_const_1000_16 = felt.const  1000 <"f">
      %59 = bool.cmp ge(%58, %felt_const_1000_16) : !felt.type<"f">, !felt.type<"f">
      bool.assert %59
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f">
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_0 : !felt.type<"f">
    struct.member @adv_0_2 : !felt.type<"f">
    struct.member @adv_0_3 : !felt.type<"f">
    struct.member @adv_1_2 : !felt.type<"f">
    struct.member @adv_0_4 : !felt.type<"f">
    struct.member @adv_0_5 : !felt.type<"f">
    struct.member @adv_1_4 : !felt.type<"f">
  }
}
