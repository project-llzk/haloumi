module attributes {llzk.fields = [#felt.field<"f", 21888242871839275222246405745257275088548364400416034343698204186575808495617>],llzk.lang = "haloumi"} {
  struct.def @fib {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    struct.member @out_1 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f">, %arg1: !felt.type<"f">) -> !struct.type<@fib<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@fib<[]>>
      function.return %self : !struct.type<@fib<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@fib<[]>>, %arg1: !felt.type<"f">, %arg2: !felt.type<"f">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 <"f">
      %0 = struct.readm %arg0[@adv_0_1] : <@fib<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_1] : <@fib<[]>>, !felt.type<"f">
      %2 = felt.add %0, %1 : !felt.type<"f">, !felt.type<"f">
      %3 = struct.readm %arg0[@out_1] : <@fib<[]>>, !felt.type<"f">
      %4 = felt.neg %3 : !felt.type<"f">
      %5 = felt.add %2, %4 : !felt.type<"f">, !felt.type<"f">
      %6 = felt.mul %felt_const_1, %5 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %6, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %7 = struct.readm %arg0[@adv_0_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %7, %arg1 : !felt.type<"f">, !felt.type<"f">
      %8 = struct.readm %arg0[@adv_1_1] : <@fib<[]>>, !felt.type<"f">
      %9 = struct.readm %arg0[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %8, %9 : !felt.type<"f">, !felt.type<"f">
      %10 = struct.readm %arg0[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %arg2, %10 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_1 : !felt.type<"f">
    struct.member @adv_1_1 : !felt.type<"f">
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type<"f"> {llzk.pub}
    struct.member @out_1 : !felt.type<"f"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"f"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"f"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %2 = struct.readm %arg0[@fib_0] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%2, %0, %1) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %3 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %4 = struct.readm %arg0[@fib_0] : <@Main<[]>>, !struct.type<@fib<[]>>
      %5 = struct.readm %4[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %3, %5 : !felt.type<"f">, !felt.type<"f">
      %6 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %7 = struct.readm %arg0[@fib_0] : <@Main<[]>>, !struct.type<@fib<[]>>
      %8 = struct.readm %7[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %6, %8 : !felt.type<"f">, !felt.type<"f">
      %9 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %10 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %11 = struct.readm %arg0[@fib_1] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%11, %9, %10) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %12 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %13 = struct.readm %arg0[@fib_1] : <@Main<[]>>, !struct.type<@fib<[]>>
      %14 = struct.readm %13[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %12, %14 : !felt.type<"f">, !felt.type<"f">
      %15 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %16 = struct.readm %arg0[@fib_1] : <@Main<[]>>, !struct.type<@fib<[]>>
      %17 = struct.readm %16[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %15, %17 : !felt.type<"f">, !felt.type<"f">
      %18 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"f">
      %19 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %20 = struct.readm %arg0[@fib_2] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%20, %18, %19) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %21 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %22 = struct.readm %arg0[@fib_2] : <@Main<[]>>, !struct.type<@fib<[]>>
      %23 = struct.readm %22[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %21, %23 : !felt.type<"f">, !felt.type<"f">
      %24 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %25 = struct.readm %arg0[@fib_2] : <@Main<[]>>, !struct.type<@fib<[]>>
      %26 = struct.readm %25[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %24, %26 : !felt.type<"f">, !felt.type<"f">
      %27 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"f">
      %28 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %29 = struct.readm %arg0[@fib_3] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%29, %27, %28) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %30 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %31 = struct.readm %arg0[@fib_3] : <@Main<[]>>, !struct.type<@fib<[]>>
      %32 = struct.readm %31[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %30, %32 : !felt.type<"f">, !felt.type<"f">
      %33 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      %34 = struct.readm %arg0[@fib_3] : <@Main<[]>>, !struct.type<@fib<[]>>
      %35 = struct.readm %34[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %33, %35 : !felt.type<"f">, !felt.type<"f">
      %36 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"f">
      %37 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      %38 = struct.readm %arg0[@fib_4] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%38, %36, %37) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %39 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      %40 = struct.readm %arg0[@fib_4] : <@Main<[]>>, !struct.type<@fib<[]>>
      %41 = struct.readm %40[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %39, %41 : !felt.type<"f">, !felt.type<"f">
      %42 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %43 = struct.readm %arg0[@fib_4] : <@Main<[]>>, !struct.type<@fib<[]>>
      %44 = struct.readm %43[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %42, %44 : !felt.type<"f">, !felt.type<"f">
      %45 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"f">
      %46 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %47 = struct.readm %arg0[@fib_5] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%47, %45, %46) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %48 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %49 = struct.readm %arg0[@fib_5] : <@Main<[]>>, !struct.type<@fib<[]>>
      %50 = struct.readm %49[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %48, %50 : !felt.type<"f">, !felt.type<"f">
      %51 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      %52 = struct.readm %arg0[@fib_5] : <@Main<[]>>, !struct.type<@fib<[]>>
      %53 = struct.readm %52[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %51, %53 : !felt.type<"f">, !felt.type<"f">
      %54 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"f">
      %55 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      %56 = struct.readm %arg0[@fib_6] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%56, %54, %55) : (!struct.type<@fib<[]>>, !felt.type<"f">, !felt.type<"f">) -> ()
      %57 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      %58 = struct.readm %arg0[@fib_6] : <@Main<[]>>, !struct.type<@fib<[]>>
      %59 = struct.readm %58[@out_0] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %57, %59 : !felt.type<"f">, !felt.type<"f">
      %60 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"f">
      %61 = struct.readm %arg0[@fib_6] : <@Main<[]>>, !struct.type<@fib<[]>>
      %62 = struct.readm %61[@out_1] : <@fib<[]>>, !felt.type<"f">
      constrain.eq %60, %62 : !felt.type<"f">, !felt.type<"f">
      %felt_const_1 = felt.const  1 <"f">
      %63 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      %64 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      %65 = felt.add %63, %64 : !felt.type<"f">, !felt.type<"f">
      %66 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"f">
      %67 = felt.neg %66 : !felt.type<"f">
      %68 = felt.add %65, %67 : !felt.type<"f">, !felt.type<"f">
      %69 = felt.mul %felt_const_1, %68 : !felt.type<"f">, !felt.type<"f">
      %felt_const_0 = felt.const  0 <"f">
      constrain.eq %69, %felt_const_0 : !felt.type<"f">, !felt.type<"f">
      %70 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %70, %arg1 : !felt.type<"f">, !felt.type<"f">
      %71 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %71, %arg2 : !felt.type<"f">, !felt.type<"f">
      %72 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"f">
      %73 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %72, %73 : !felt.type<"f">, !felt.type<"f">
      %74 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"f">
      %75 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"f">
      constrain.eq %74, %75 : !felt.type<"f">, !felt.type<"f">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"f"> 
    struct.member @adv_1_0 : !felt.type<"f"> 
    struct.member @fib_0 : !struct.type<@fib<[]>>
    struct.member @adv_2_1 : !felt.type<"f">
    struct.member @fib_1 : !struct.type<@fib<[]>>
    struct.member @adv_2_2 : !felt.type<"f">
    struct.member @fib_2 : !struct.type<@fib<[]>>
    struct.member @adv_2_3 : !felt.type<"f">
    struct.member @fib_3 : !struct.type<@fib<[]>>
    struct.member @adv_2_4 : !felt.type<"f">
    struct.member @fib_4 : !struct.type<@fib<[]>>
    struct.member @adv_2_5 : !felt.type<"f">
    struct.member @fib_5 : !struct.type<@fib<[]>>
    struct.member @adv_2_6 : !felt.type<"f">
    struct.member @fib_6 : !struct.type<@fib<[]>>
    struct.member @adv_2_7 : !felt.type<"f">
    struct.member @adv_2_0 : !felt.type<"f"> 
  }
}
