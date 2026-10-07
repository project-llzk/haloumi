module attributes { llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>> } {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_1 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_2 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops, function.allow_verif_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type<"bn254">, !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %3 = felt.neg %2 : !felt.type<"bn254">
      %4 = felt.add %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = felt.mul %felt_const_1, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %5, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_0 = felt.const  1 <"bn254">
      %6 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %8 = felt.mul %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      %10 = felt.neg %9 : !felt.type<"bn254">
      %11 = felt.add %8, %10 : !felt.type<"bn254">, !felt.type<"bn254">
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_1 = felt.const  0 <"bn254">
      constrain.eq %12, %felt_const_0_1 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_2 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %13 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %14 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3, %13 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %16 = felt.neg %15 : !felt.type<"bn254">
      %17 = felt.add %14, %16 : !felt.type<"bn254">, !felt.type<"bn254">
      %18 = felt.mul %felt_const_1_2, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_4 = felt.const  0 <"bn254">
      constrain.eq %18, %felt_const_0_4 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_5 = felt.const  1 <"bn254">
      %19 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %20 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %21 = felt.mul %19, %20 : !felt.type<"bn254">, !felt.type<"bn254">
      %22 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      %23 = felt.neg %22 : !felt.type<"bn254">
      %24 = felt.add %21, %23 : !felt.type<"bn254">, !felt.type<"bn254">
      %25 = felt.mul %felt_const_1_5, %24 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_6 = felt.const  0 <"bn254">
      constrain.eq %25, %felt_const_0_6 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_7 = felt.const  1 <"bn254">
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616 <"bn254">
      %26 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %27 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8, %26 : !felt.type<"bn254">, !felt.type<"bn254">
      %28 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %29 = felt.neg %28 : !felt.type<"bn254">
      %30 = felt.add %27, %29 : !felt.type<"bn254">, !felt.type<"bn254">
      %31 = felt.mul %felt_const_1_7, %30 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_9 = felt.const  0 <"bn254">
      constrain.eq %31, %felt_const_0_9 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_10 = felt.const  1 <"bn254">
      %32 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %33 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %34 = felt.mul %32, %33 : !felt.type<"bn254">, !felt.type<"bn254">
      %35 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      %36 = felt.neg %35 : !felt.type<"bn254">
      %37 = felt.add %34, %36 : !felt.type<"bn254">, !felt.type<"bn254">
      %38 = felt.mul %felt_const_1_10, %37 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_11 = felt.const  0 <"bn254">
      constrain.eq %38, %felt_const_0_11 : !felt.type<"bn254">, !felt.type<"bn254">
      %39 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %40 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %39, %40 : !felt.type<"bn254">, !felt.type<"bn254">
      %41 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %42 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %41, %42 : !felt.type<"bn254">, !felt.type<"bn254">
      %43 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %44 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %43, %44 : !felt.type<"bn254">, !felt.type<"bn254">
      %45 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      %46 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %45, %46 : !felt.type<"bn254">, !felt.type<"bn254">
      %47 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      %48 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %47, %48 : !felt.type<"bn254">, !felt.type<"bn254">
      %49 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      %50 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %49, %50 : !felt.type<"bn254">, !felt.type<"bn254">
      %51 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %51, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %52 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
       %felt_const_1000 = felt.const  1000 : <"bn254">
      %53 = bool.cmp lt(%52, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
       %54 = bool.not %53 : i1
       %55 = cast.tofelt %54 : i1, !felt.type<"bn254">
      %felt_const_0_12 = felt.const  0 : <"bn254">
      constrain.eq %55, %felt_const_0_12 : !felt.type<"bn254">, !felt.type<"bn254">
      %56 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %felt_const_1000_13 = felt.const  1000 : <"bn254">
      %57 = bool.cmp ge(%56, %felt_const_1000_13) : !felt.type<"bn254">, !felt.type<"bn254">
       %58 = bool.not %57 : i1
       %59 = cast.tofelt %58 : i1, !felt.type<"bn254">
      %felt_const_0_14 = felt.const  0 : <"bn254">
      constrain.eq %59, %felt_const_0_14 : !felt.type<"bn254">, !felt.type<"bn254">
      %60 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %felt_const_1000_15 = felt.const  1000 : <"bn254">
      %61 = bool.cmp lt(%60, %felt_const_1000_15) : !felt.type<"bn254">, !felt.type<"bn254">
       %62 = bool.not %61 : i1
       %63 = cast.tofelt %62 : i1, !felt.type<"bn254">
      %felt_const_0_16 = felt.const  0 : <"bn254">
      constrain.eq %63, %felt_const_0_16 : !felt.type<"bn254">, !felt.type<"bn254">
      %64 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %felt_const_1000_17 = felt.const  1000 : <"bn254">
      %65 = bool.cmp ge(%64, %felt_const_1000_17) : !felt.type<"bn254">, !felt.type<"bn254">
      %66 = bool.not %65 : i1
      %67 = cast.tofelt %66 : i1, !felt.type<"bn254">
       %felt_const_0_18 = felt.const  0 : <"bn254">
      constrain.eq %67, %felt_const_0_18 : !felt.type<"bn254">, !felt.type<"bn254">
      %68 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
       %felt_const_1000_19 = felt.const  1000 : <"bn254">
      %69 = bool.cmp lt(%68, %felt_const_1000_19) : !felt.type<"bn254">, !felt.type<"bn254">
      %70 = bool.not %69 : i1
      %71 = cast.tofelt %70 : i1, !felt.type<"bn254">
       %felt_const_0_20 = felt.const  0 : <"bn254">
      constrain.eq %71, %felt_const_0_20 : !felt.type<"bn254">, !felt.type<"bn254">
      %72 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
       %felt_const_1000_21 = felt.const  1000 : <"bn254">
      %73 = bool.cmp ge(%72, %felt_const_1000_21) : !felt.type<"bn254">, !felt.type<"bn254">
      %74 = bool.not %73 : i1
      %75 = cast.tofelt %74 : i1, !felt.type<"bn254">
       %felt_const_0_22 = felt.const  0 : <"bn254">
      constrain.eq %75, %felt_const_0_22 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254">
    struct.member @adv_0_1 : !felt.type<"bn254">
    struct.member @adv_1_0 : !felt.type<"bn254">
    struct.member @adv_0_2 : !felt.type<"bn254">
    struct.member @adv_0_3 : !felt.type<"bn254">
    struct.member @adv_1_2 : !felt.type<"bn254">
    struct.member @adv_0_4 : !felt.type<"bn254">
    struct.member @adv_0_5 : !felt.type<"bn254">
    struct.member @adv_1_4 : !felt.type<"bn254">
    struct.member @adv_3_0 : !felt.type<"bn254">
  }
}
