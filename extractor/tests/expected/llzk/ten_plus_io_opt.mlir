module attributes { llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>> } {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_1 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_2 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_3 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_4 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_5 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_6 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_7 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_8 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_9 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_10 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg3: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg4: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg5: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg6: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg7: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg8: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg9: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg10: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg3: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg4: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg5: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg6: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg7: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg8: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg9: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg10: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg11: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops, function.allow_verif_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = felt.neg %0 : !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = felt.mul %0, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %3, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      %6 = felt.neg %5 : !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %8 = felt.mul %5, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %11 = felt.neg %10 : !felt.type<"bn254">
      %12 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %11, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = felt.mul %10, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %14 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %13, %14 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      %16 = felt.neg %15 : !felt.type<"bn254">
      %17 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %16, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %18 = felt.mul %15, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %19 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %18, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      %20 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %21 = felt.neg %20 : !felt.type<"bn254">
      %22 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %21, %22 : !felt.type<"bn254">, !felt.type<"bn254">
      %23 = felt.mul %20, %22 : !felt.type<"bn254">, !felt.type<"bn254">
      %24 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %23, %24 : !felt.type<"bn254">, !felt.type<"bn254">
      %25 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      %26 = felt.neg %25 : !felt.type<"bn254">
      %27 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %26, %27 : !felt.type<"bn254">, !felt.type<"bn254">
      %28 = felt.mul %25, %27 : !felt.type<"bn254">, !felt.type<"bn254">
      %29 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %28, %29 : !felt.type<"bn254">, !felt.type<"bn254">
      %30 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"bn254">
      %31 = felt.neg %30 : !felt.type<"bn254">
      %32 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %31, %32 : !felt.type<"bn254">, !felt.type<"bn254">
      %33 = felt.mul %30, %32 : !felt.type<"bn254">, !felt.type<"bn254">
      %34 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %33, %34 : !felt.type<"bn254">, !felt.type<"bn254">
      %35 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"bn254">
      %36 = felt.neg %35 : !felt.type<"bn254">
      %37 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %36, %37 : !felt.type<"bn254">, !felt.type<"bn254">
      %38 = felt.mul %35, %37 : !felt.type<"bn254">, !felt.type<"bn254">
      %39 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %38, %39 : !felt.type<"bn254">, !felt.type<"bn254">
      %40 = struct.readm %arg0[@adv_0_8] : <@Main<[]>>, !felt.type<"bn254">
      %41 = felt.neg %40 : !felt.type<"bn254">
      %42 = struct.readm %arg0[@adv_1_8] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %41, %42 : !felt.type<"bn254">, !felt.type<"bn254">
      %43 = felt.mul %40, %42 : !felt.type<"bn254">, !felt.type<"bn254">
      %44 = struct.readm %arg0[@adv_2_8] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %43, %44 : !felt.type<"bn254">, !felt.type<"bn254">
      %45 = struct.readm %arg0[@adv_0_9] : <@Main<[]>>, !felt.type<"bn254">
      %46 = felt.neg %45 : !felt.type<"bn254">
      %47 = struct.readm %arg0[@adv_1_9] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %46, %47 : !felt.type<"bn254">, !felt.type<"bn254">
      %48 = felt.mul %45, %47 : !felt.type<"bn254">, !felt.type<"bn254">
      %49 = struct.readm %arg0[@adv_2_9] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %48, %49 : !felt.type<"bn254">, !felt.type<"bn254">
      %50 = struct.readm %arg0[@adv_0_10] : <@Main<[]>>, !felt.type<"bn254">
      %51 = felt.neg %50 : !felt.type<"bn254">
      %52 = struct.readm %arg0[@adv_1_10] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %51, %52 : !felt.type<"bn254">, !felt.type<"bn254">
      %53 = felt.mul %50, %52 : !felt.type<"bn254">, !felt.type<"bn254">
      %54 = struct.readm %arg0[@adv_2_10] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %53, %54 : !felt.type<"bn254">, !felt.type<"bn254">
      %55 = struct.readm %arg0[@adv_3_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %0, %55 : !felt.type<"bn254">, !felt.type<"bn254">
      %56 = struct.readm %arg0[@adv_3_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %5, %56 : !felt.type<"bn254">, !felt.type<"bn254">
      %57 = struct.readm %arg0[@adv_3_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %10, %57 : !felt.type<"bn254">, !felt.type<"bn254">
      %58 = struct.readm %arg0[@adv_3_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %15, %58 : !felt.type<"bn254">, !felt.type<"bn254">
      %59 = struct.readm %arg0[@adv_3_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %20, %59 : !felt.type<"bn254">, !felt.type<"bn254">
      %60 = struct.readm %arg0[@adv_3_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %25, %60 : !felt.type<"bn254">, !felt.type<"bn254">
      %61 = struct.readm %arg0[@adv_3_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %30, %61 : !felt.type<"bn254">, !felt.type<"bn254">
      %62 = struct.readm %arg0[@adv_3_7] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %35, %62 : !felt.type<"bn254">, !felt.type<"bn254">
      %63 = struct.readm %arg0[@adv_3_8] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %40, %63 : !felt.type<"bn254">, !felt.type<"bn254">
      %64 = struct.readm %arg0[@adv_3_9] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %45, %64 : !felt.type<"bn254">, !felt.type<"bn254">
      %65 = struct.readm %arg0[@adv_3_10] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %50, %65 : !felt.type<"bn254">, !felt.type<"bn254">
      %66 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %4, %66 : !felt.type<"bn254">, !felt.type<"bn254">
      %67 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %9, %67 : !felt.type<"bn254">, !felt.type<"bn254">
      %68 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %14, %68 : !felt.type<"bn254">, !felt.type<"bn254">
      %69 = struct.readm %arg0[@out_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %19, %69 : !felt.type<"bn254">, !felt.type<"bn254">
      %70 = struct.readm %arg0[@out_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %24, %70 : !felt.type<"bn254">, !felt.type<"bn254">
      %71 = struct.readm %arg0[@out_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %29, %71 : !felt.type<"bn254">, !felt.type<"bn254">
      %72 = struct.readm %arg0[@out_6] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %34, %72 : !felt.type<"bn254">, !felt.type<"bn254">
      %73 = struct.readm %arg0[@out_7] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %39, %73 : !felt.type<"bn254">, !felt.type<"bn254">
      %74 = struct.readm %arg0[@out_8] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %44, %74 : !felt.type<"bn254">, !felt.type<"bn254">
      %75 = struct.readm %arg0[@out_9] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %49, %75 : !felt.type<"bn254">, !felt.type<"bn254">
      %76 = struct.readm %arg0[@out_10] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %54, %76 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %55, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %56, %arg2 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %57, %arg3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %58, %arg4 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %59, %arg5 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %60, %arg6 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %61, %arg7 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %62, %arg8 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %63, %arg9 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %64, %arg10 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %65, %arg11 : !felt.type<"bn254">, !felt.type<"bn254">
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
    struct.member @adv_0_8 : !felt.type<"bn254">
    struct.member @adv_1_8 : !felt.type<"bn254">
    struct.member @adv_2_8 : !felt.type<"bn254">
    struct.member @adv_0_9 : !felt.type<"bn254">
    struct.member @adv_1_9 : !felt.type<"bn254">
    struct.member @adv_2_9 : !felt.type<"bn254">
    struct.member @adv_0_10 : !felt.type<"bn254">
    struct.member @adv_1_10 : !felt.type<"bn254">
    struct.member @adv_2_10 : !felt.type<"bn254">
    struct.member @adv_3_0 : !felt.type<"bn254">
    struct.member @adv_3_1 : !felt.type<"bn254">
    struct.member @adv_3_2 : !felt.type<"bn254">
    struct.member @adv_3_3 : !felt.type<"bn254">
    struct.member @adv_3_4 : !felt.type<"bn254">
    struct.member @adv_3_5 : !felt.type<"bn254">
    struct.member @adv_3_6 : !felt.type<"bn254">
    struct.member @adv_3_7 : !felt.type<"bn254">
    struct.member @adv_3_8 : !felt.type<"bn254">
    struct.member @adv_3_9 : !felt.type<"bn254">
    struct.member @adv_3_10 : !felt.type<"bn254">
  }
}
