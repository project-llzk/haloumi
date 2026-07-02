module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    struct.member @out_1 : !felt.type {llzk.pub}
    struct.member @out_2 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616, %0 : !felt.type, !felt.type
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %3 = felt.neg %2 : !felt.type
      %4 = felt.add %1, %3 : !felt.type, !felt.type
      %5 = felt.mul %felt_const_1, %4 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %5, %felt_const_0 : !felt.type, !felt.type
      %felt_const_1_0 = felt.const  1
      %6 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %8 = felt.mul %6, %7 : !felt.type, !felt.type
      %9 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %10 = felt.neg %9 : !felt.type
      %11 = felt.add %8, %10 : !felt.type, !felt.type
      %12 = felt.mul %felt_const_1_0, %11 : !felt.type, !felt.type
      %felt_const_0_1 = felt.const  0
      constrain.eq %12, %felt_const_0_1 : !felt.type, !felt.type
      %felt_const_1_2 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %13 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %14 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_3, %13 : !felt.type, !felt.type
      %15 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %16 = felt.neg %15 : !felt.type
      %17 = felt.add %14, %16 : !felt.type, !felt.type
      %18 = felt.mul %felt_const_1_2, %17 : !felt.type, !felt.type
      %felt_const_0_4 = felt.const  0
      constrain.eq %18, %felt_const_0_4 : !felt.type, !felt.type
      %felt_const_1_5 = felt.const  1
      %19 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %20 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %21 = felt.mul %19, %20 : !felt.type, !felt.type
      %22 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type
      %23 = felt.neg %22 : !felt.type
      %24 = felt.add %21, %23 : !felt.type, !felt.type
      %25 = felt.mul %felt_const_1_5, %24 : !felt.type, !felt.type
      %felt_const_0_6 = felt.const  0
      constrain.eq %25, %felt_const_0_6 : !felt.type, !felt.type
      %felt_const_1_7 = felt.const  1
      %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8 = felt.const  21888242871839275222246405745257275088548364400416034343698204186575808495616
      %26 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %27 = felt.mul %felt_const_21888242871839275222246405745257275088548364400416034343698204186575808495616_8, %26 : !felt.type, !felt.type
      %28 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %29 = felt.neg %28 : !felt.type
      %30 = felt.add %27, %29 : !felt.type, !felt.type
      %31 = felt.mul %felt_const_1_7, %30 : !felt.type, !felt.type
      %felt_const_0_9 = felt.const  0
      constrain.eq %31, %felt_const_0_9 : !felt.type, !felt.type
      %felt_const_1_10 = felt.const  1
      %32 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %33 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %34 = felt.mul %32, %33 : !felt.type, !felt.type
      %35 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type
      %36 = felt.neg %35 : !felt.type
      %37 = felt.add %34, %36 : !felt.type, !felt.type
      %38 = felt.mul %felt_const_1_10, %37 : !felt.type, !felt.type
      %felt_const_0_11 = felt.const  0
      constrain.eq %38, %felt_const_0_11 : !felt.type, !felt.type
      %39 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %39, %arg1 : !felt.type, !felt.type
      %40 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      constrain.eq %40, %arg1 : !felt.type, !felt.type
      %41 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      constrain.eq %41, %arg1 : !felt.type, !felt.type
      %42 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %43 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %42, %43 : !felt.type, !felt.type
      %44 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type
      %45 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type
      constrain.eq %44, %45 : !felt.type, !felt.type
      %46 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type
      %47 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type
      constrain.eq %46, %47 : !felt.type, !felt.type
      %48 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %felt_const_1000 = felt.const  1000
      %49 = bool.cmp lt(%48, %felt_const_1000) : !felt.type, !felt.type
      bool.assert %49
      %50 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %felt_const_1000_12 = felt.const  1000
      %51 = bool.cmp ge(%50, %felt_const_1000_12) : !felt.type, !felt.type
      bool.assert %51
      %52 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %felt_const_1000_13 = felt.const  1000
      %53 = bool.cmp lt(%52, %felt_const_1000_13) : !felt.type, !felt.type
      bool.assert %53
      %54 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %felt_const_1000_14 = felt.const  1000
      %55 = bool.cmp ge(%54, %felt_const_1000_14) : !felt.type, !felt.type
      bool.assert %55
      %56 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %felt_const_1000_15 = felt.const  1000
      %57 = bool.cmp lt(%56, %felt_const_1000_15) : !felt.type, !felt.type
      bool.assert %57
      %58 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %felt_const_1000_16 = felt.const  1000
      %59 = bool.cmp ge(%58, %felt_const_1000_16) : !felt.type, !felt.type
      bool.assert %59
      function.return
    }
    struct.member @adv_0_0 : !felt.type
    struct.member @adv_0_1 : !felt.type
    struct.member @adv_1_0 : !felt.type
    struct.member @adv_0_2 : !felt.type
    struct.member @adv_0_3 : !felt.type
    struct.member @adv_1_2 : !felt.type
    struct.member @adv_0_4 : !felt.type
    struct.member @adv_0_5 : !felt.type
    struct.member @adv_1_4 : !felt.type
  }
}
