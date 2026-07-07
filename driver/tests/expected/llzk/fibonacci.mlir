module attributes { llzk.lang = "halo2"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"bn254">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      %2 = felt.add %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      %4 = felt.neg %3 : !felt.type<"bn254">
      %5 = felt.add %2, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0 = felt.const  0 <"bn254">
      constrain.eq %6, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_0 = felt.const  1 <"bn254">
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %8 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"bn254">
      %9 = felt.add %7, %8 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      %11 = felt.neg %10 : !felt.type<"bn254">
      %12 = felt.add %9, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = felt.mul %felt_const_1_0, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_1 = felt.const  0 <"bn254">
      constrain.eq %13, %felt_const_0_1 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_2 = felt.const  1 <"bn254">
      %14 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %15 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      %16 = felt.add %14, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %17 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      %18 = felt.neg %17 : !felt.type<"bn254">
      %19 = felt.add %16, %18 : !felt.type<"bn254">, !felt.type<"bn254">
      %20 = felt.mul %felt_const_1_2, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_3 = felt.const  0 <"bn254">
      constrain.eq %20, %felt_const_0_3 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_4 = felt.const  1 <"bn254">
      %21 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %22 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"bn254">
      %23 = felt.add %21, %22 : !felt.type<"bn254">, !felt.type<"bn254">
      %24 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      %25 = felt.neg %24 : !felt.type<"bn254">
      %26 = felt.add %23, %25 : !felt.type<"bn254">, !felt.type<"bn254">
      %27 = felt.mul %felt_const_1_4, %26 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_5 = felt.const  0 <"bn254">
      constrain.eq %27, %felt_const_0_5 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_6 = felt.const  1 <"bn254">
      %28 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %29 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      %30 = felt.add %28, %29 : !felt.type<"bn254">, !felt.type<"bn254">
      %31 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      %32 = felt.neg %31 : !felt.type<"bn254">
      %33 = felt.add %30, %32 : !felt.type<"bn254">, !felt.type<"bn254">
      %34 = felt.mul %felt_const_1_6, %33 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_7 = felt.const  0 <"bn254">
      constrain.eq %34, %felt_const_0_7 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_8 = felt.const  1 <"bn254">
      %35 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %36 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"bn254">
      %37 = felt.add %35, %36 : !felt.type<"bn254">, !felt.type<"bn254">
      %38 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      %39 = felt.neg %38 : !felt.type<"bn254">
      %40 = felt.add %37, %39 : !felt.type<"bn254">, !felt.type<"bn254">
      %41 = felt.mul %felt_const_1_8, %40 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_9 = felt.const  0 <"bn254">
      constrain.eq %41, %felt_const_0_9 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_10 = felt.const  1 <"bn254">
      %42 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"bn254">
      %43 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"bn254">
      %44 = felt.add %42, %43 : !felt.type<"bn254">, !felt.type<"bn254">
      %45 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      %46 = felt.neg %45 : !felt.type<"bn254">
      %47 = felt.add %44, %46 : !felt.type<"bn254">, !felt.type<"bn254">
      %48 = felt.mul %felt_const_1_10, %47 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_11 = felt.const  0 <"bn254">
      constrain.eq %48, %felt_const_0_11 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_1_12 = felt.const  1 <"bn254">
      %49 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"bn254">
      %50 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"bn254">
      %51 = felt.add %49, %50 : !felt.type<"bn254">, !felt.type<"bn254">
      %52 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"bn254">
      %53 = felt.neg %52 : !felt.type<"bn254">
      %54 = felt.add %51, %53 : !felt.type<"bn254">, !felt.type<"bn254">
      %55 = felt.mul %felt_const_1_12, %54 : !felt.type<"bn254">, !felt.type<"bn254">
      %felt_const_0_13 = felt.const  0 <"bn254">
      constrain.eq %55, %felt_const_0_13 : !felt.type<"bn254">, !felt.type<"bn254">
      %56 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %56, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %57 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %58 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %57, %58 : !felt.type<"bn254">, !felt.type<"bn254">
      %59 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %60 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %59, %60 : !felt.type<"bn254">, !felt.type<"bn254">
      %61 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %62 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %61, %62 : !felt.type<"bn254">, !felt.type<"bn254">
      %63 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %64 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %63, %64 : !felt.type<"bn254">, !felt.type<"bn254">
      %65 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %66 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %65, %66 : !felt.type<"bn254">, !felt.type<"bn254">
      %67 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"bn254">
      %68 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %67, %68 : !felt.type<"bn254">, !felt.type<"bn254">
      %69 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"bn254">
      %70 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %69, %70 : !felt.type<"bn254">, !felt.type<"bn254">
      %71 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %71, %arg2 : !felt.type<"bn254">, !felt.type<"bn254">
      %72 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"bn254">
      %73 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %72, %73 : !felt.type<"bn254">, !felt.type<"bn254">
      %74 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      %75 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %74, %75 : !felt.type<"bn254">, !felt.type<"bn254">
      %76 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"bn254">
      %77 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %76, %77 : !felt.type<"bn254">, !felt.type<"bn254">
      %78 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      %79 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %78, %79 : !felt.type<"bn254">, !felt.type<"bn254">
      %80 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"bn254">
      %81 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %80, %81 : !felt.type<"bn254">, !felt.type<"bn254">
      %82 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"bn254">
      %83 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %82, %83 : !felt.type<"bn254">, !felt.type<"bn254">
      %84 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"bn254">
      %85 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %84, %85 : !felt.type<"bn254">, !felt.type<"bn254">
      %86 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"bn254">
      %87 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %86, %87 : !felt.type<"bn254">, !felt.type<"bn254">
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
