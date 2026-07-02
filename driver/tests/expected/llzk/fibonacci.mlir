module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"f">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %2 = felt.add %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      %4 = felt.neg %3 : !felt.type<"f">
      %5 = felt.add %2, %4 : !felt.type<"f">, !felt.type<"f">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %6, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_0 = felt.const  1 <"f">
      %7 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %8 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"f">
      %9 = felt.add %7, %8 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %11 = felt.neg %10 : !felt.type<"f">
      %12 = felt.add %9, %11 : !felt.type<"f">, !felt.type<"f">
      %13 = felt.mul %felt_const_1_0, %12 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_1 = felt.const  0 <"f">
      constrain.eq %13, %felt_const_0_1 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_2 = felt.const  1 <"f">
      %14 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %15 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      %16 = felt.add %14, %15 : !felt.type<"f">, !felt.type<"f">
      %17 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %18 = felt.neg %17 : !felt.type<"f">
      %19 = felt.add %16, %18 : !felt.type<"f">, !felt.type<"f">
      %20 = felt.mul %felt_const_1_2, %19 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_3 = felt.const  0 <"f">
      constrain.eq %20, %felt_const_0_3 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_4 = felt.const  1 <"f">
      %21 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %22 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"f">
      %23 = felt.add %21, %22 : !felt.type<"f">, !felt.type<"f">
      %24 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %25 = felt.neg %24 : !felt.type<"f">
      %26 = felt.add %23, %25 : !felt.type<"f">, !felt.type<"f">
      %27 = felt.mul %felt_const_1_4, %26 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_5 = felt.const  0 <"f">
      constrain.eq %27, %felt_const_0_5 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_6 = felt.const  1 <"f">
      %28 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %29 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      %30 = felt.add %28, %29 : !felt.type<"f">, !felt.type<"f">
      %31 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      %32 = felt.neg %31 : !felt.type<"f">
      %33 = felt.add %30, %32 : !felt.type<"f">, !felt.type<"f">
      %34 = felt.mul %felt_const_1_6, %33 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_7 = felt.const  0 <"f">
      constrain.eq %34, %felt_const_0_7 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_8 = felt.const  1 <"f">
      %35 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %36 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"f">
      %37 = felt.add %35, %36 : !felt.type<"f">, !felt.type<"f">
      %38 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %39 = felt.neg %38 : !felt.type<"f">
      %40 = felt.add %37, %39 : !felt.type<"f">, !felt.type<"f">
      %41 = felt.mul %felt_const_1_8, %40 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_9 = felt.const  0 <"f">
      constrain.eq %41, %felt_const_0_9 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_10 = felt.const  1 <"f">
      %42 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"f">
      %43 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"f">
      %44 = felt.add %42, %43 : !felt.type<"f">, !felt.type<"f">
      %45 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      %46 = felt.neg %45 : !felt.type<"f">
      %47 = felt.add %44, %46 : !felt.type<"f">, !felt.type<"f">
      %48 = felt.mul %felt_const_1_10, %47 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_11 = felt.const  0 <"f">
      constrain.eq %48, %felt_const_0_11 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1_12 = felt.const  1 <"f">
      %49 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"f">
      %50 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"f">
      %51 = felt.add %49, %50 : !felt.type<"f">, !felt.type<"f">
      %52 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"f">
      %53 = felt.neg %52 : !felt.type<"f">
      %54 = felt.add %51, %53 : !felt.type<"f">, !felt.type<"f">
      %55 = felt.mul %felt_const_1_12, %54 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0_13 = felt.const  0 <"f">
      constrain.eq %55, %felt_const_0_13 : !felt.type<"f">, !felt.type<"f">
      %56 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %56, %arg1 : !felt.type<"f">, !felt.type<"f">
      %57 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"f">
      %58 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %57, %58 : !felt.type<"f">, !felt.type<"f">
      %59 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"f">
      %60 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %59, %60 : !felt.type<"f">, !felt.type<"f">
      %61 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"f">
      %62 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %61, %62 : !felt.type<"f">, !felt.type<"f">
      %63 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"f">
      %64 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %63, %64 : !felt.type<"f">, !felt.type<"f">
      %65 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"f">
      %66 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %65, %66 : !felt.type<"f">, !felt.type<"f">
      %67 = struct.readm %arg0[@adv_0_6] : <@Main<[]>>, !felt.type<"f">
      %68 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %67, %68 : !felt.type<"f">, !felt.type<"f">
      %69 = struct.readm %arg0[@adv_0_7] : <@Main<[]>>, !felt.type<"f">
      %70 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %69, %70 : !felt.type<"f">, !felt.type<"f">
      %71 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %71, %arg2 : !felt.type<"f">, !felt.type<"f">
      %72 = struct.readm %arg0[@adv_1_1] : <@Main<[]>>, !felt.type<"f">
      %73 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %72, %73 : !felt.type<"f">, !felt.type<"f">
      %74 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"f">
      %75 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %74, %75 : !felt.type<"f">, !felt.type<"f">
      %76 = struct.readm %arg0[@adv_1_3] : <@Main<[]>>, !felt.type<"f">
      %77 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %76, %77 : !felt.type<"f">, !felt.type<"f">
      %78 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"f">
      %79 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %78, %79 : !felt.type<"f">, !felt.type<"f">
      %80 = struct.readm %arg0[@adv_1_5] : <@Main<[]>>, !felt.type<"f">
      %81 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %80, %81 : !felt.type<"f">, !felt.type<"f">
      %82 = struct.readm %arg0[@adv_1_6] : <@Main<[]>>, !felt.type<"f">
      %83 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %82, %83 : !felt.type<"f">, !felt.type<"f">
      %84 = struct.readm %arg0[@adv_1_7] : <@Main<[]>>, !felt.type<"f">
      %85 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %84, %85 : !felt.type<"f">, !felt.type<"f">
      %86 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"f">
      %87 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %86, %87 : !felt.type<"f">, !felt.type<"f">
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
