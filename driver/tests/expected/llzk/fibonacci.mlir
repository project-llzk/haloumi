module attributes {llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type {llzk.pub}
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}, %arg1: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      %2 = felt.add %0, %1 : !felt.type, !felt.type
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      %4 = felt.neg %3 : !felt.type
      %5 = felt.add %2, %4 : !felt.type, !felt.type
      %6 = felt.mul %felt_const_1, %5 : !felt.type, !felt.type
      %felt_const_0 = felt.const  0
      constrain.eq %6, %felt_const_0 : !felt.type, !felt.type
      %felt_const_1_0 = felt.const  1
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %8 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type
      %9 = felt.add %7, %8 : !felt.type, !felt.type
      %10 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      %11 = felt.neg %10 : !felt.type
      %12 = felt.add %9, %11 : !felt.type, !felt.type
      %13 = felt.mul %felt_const_1_0, %12 : !felt.type, !felt.type
      %felt_const_0_1 = felt.const  0
      constrain.eq %13, %felt_const_0_1 : !felt.type, !felt.type
      %felt_const_1_2 = felt.const  1
      %14 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %15 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type
      %16 = felt.add %14, %15 : !felt.type, !felt.type
      %17 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      %18 = felt.neg %17 : !felt.type
      %19 = felt.add %16, %18 : !felt.type, !felt.type
      %20 = felt.mul %felt_const_1_2, %19 : !felt.type, !felt.type
      %felt_const_0_3 = felt.const  0
      constrain.eq %20, %felt_const_0_3 : !felt.type, !felt.type
      %felt_const_1_4 = felt.const  1
      %21 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %22 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type
      %23 = felt.add %21, %22 : !felt.type, !felt.type
      %24 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      %25 = felt.neg %24 : !felt.type
      %26 = felt.add %23, %25 : !felt.type, !felt.type
      %27 = felt.mul %felt_const_1_4, %26 : !felt.type, !felt.type
      %felt_const_0_5 = felt.const  0
      constrain.eq %27, %felt_const_0_5 : !felt.type, !felt.type
      %felt_const_1_6 = felt.const  1
      %28 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %29 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type
      %30 = felt.add %28, %29 : !felt.type, !felt.type
      %31 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type
      %32 = felt.neg %31 : !felt.type
      %33 = felt.add %30, %32 : !felt.type, !felt.type
      %34 = felt.mul %felt_const_1_6, %33 : !felt.type, !felt.type
      %felt_const_0_7 = felt.const  0
      constrain.eq %34, %felt_const_0_7 : !felt.type, !felt.type
      %felt_const_1_8 = felt.const  1
      %35 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %36 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type
      %37 = felt.add %35, %36 : !felt.type, !felt.type
      %38 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      %39 = felt.neg %38 : !felt.type
      %40 = felt.add %37, %39 : !felt.type, !felt.type
      %41 = felt.mul %felt_const_1_8, %40 : !felt.type, !felt.type
      %felt_const_0_9 = felt.const  0
      constrain.eq %41, %felt_const_0_9 : !felt.type, !felt.type
      %felt_const_1_10 = felt.const  1
      %42 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type
      %43 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type
      %44 = felt.add %42, %43 : !felt.type, !felt.type
      %45 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      %46 = felt.neg %45 : !felt.type
      %47 = felt.add %44, %46 : !felt.type, !felt.type
      %48 = felt.mul %felt_const_1_10, %47 : !felt.type, !felt.type
      %felt_const_0_11 = felt.const  0
      constrain.eq %48, %felt_const_0_11 : !felt.type, !felt.type
      %felt_const_1_12 = felt.const  1
      %49 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type
      %50 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type
      %51 = felt.add %49, %50 : !felt.type, !felt.type
      %52 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type
      %53 = felt.neg %52 : !felt.type
      %54 = felt.add %51, %53 : !felt.type, !felt.type
      %55 = felt.mul %felt_const_1_12, %54 : !felt.type, !felt.type
      %felt_const_0_13 = felt.const  0
      constrain.eq %55, %felt_const_0_13 : !felt.type, !felt.type
      %56 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type
      constrain.eq %56, %arg1 : !felt.type, !felt.type
      %57 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type
      %58 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      constrain.eq %57, %58 : !felt.type, !felt.type
      %59 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type
      %60 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      constrain.eq %59, %60 : !felt.type, !felt.type
      %61 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type
      %62 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      constrain.eq %61, %62 : !felt.type, !felt.type
      %63 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type
      %64 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      constrain.eq %63, %64 : !felt.type, !felt.type
      %65 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type
      %66 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      constrain.eq %65, %66 : !felt.type, !felt.type
      %67 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type
      %68 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type
      constrain.eq %67, %68 : !felt.type, !felt.type
      %69 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type
      %70 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      constrain.eq %69, %70 : !felt.type, !felt.type
      %71 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type
      constrain.eq %71, %arg2 : !felt.type, !felt.type
      %72 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type
      %73 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type
      constrain.eq %72, %73 : !felt.type, !felt.type
      %74 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type
      %75 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type
      constrain.eq %74, %75 : !felt.type, !felt.type
      %76 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type
      %77 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type
      constrain.eq %76, %77 : !felt.type, !felt.type
      %78 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type
      %79 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type
      constrain.eq %78, %79 : !felt.type, !felt.type
      %80 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type
      %81 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type
      constrain.eq %80, %81 : !felt.type, !felt.type
      %82 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type
      %83 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type
      constrain.eq %82, %83 : !felt.type, !felt.type
      %84 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type
      %85 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type
      constrain.eq %84, %85 : !felt.type, !felt.type
      %86 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type
      %87 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type
      constrain.eq %86, %87 : !felt.type, !felt.type
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
