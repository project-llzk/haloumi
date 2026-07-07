module attributes { llzk.lang = "halo2"} {
  struct.def @fib {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_1 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254">, %arg1: !felt.type<"bn254">) -> !struct.type<@fib<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@fib<[]>>
      function.return %self : !struct.type<@fib<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@fib<[]>>, %arg1: !felt.type<"bn254">, %arg2: !felt.type<"bn254">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_1] : <@fib<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_1] : <@fib<[]>>, !felt.type<"bn254">
      %2 = felt.add %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = struct.readm %arg0[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %2, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %1, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %arg2, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_1 : !felt.type<"bn254">
    struct.member @adv_1_1 : !felt.type<"bn254">
  }
  struct.def @Main {
    struct.member @out_0 : !felt.type<"bn254"> {llzk.pub}
    struct.member @out_1 : !felt.type<"bn254"> {llzk.pub}
    function.def @compute(%arg0: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type<"bn254"> {llzk.pub = #llzk.pub}, %arg2: !felt.type<"bn254"> {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      %2 = struct.readm %arg0[@fib_0] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%2, %0, %1) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %3 = struct.readm %2[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %1, %3 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_2_1] : <@Main<[]>>, !felt.type<"bn254">
      %5 = struct.readm %2[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %4, %5 : !felt.type<"bn254">, !felt.type<"bn254">
      %6 = struct.readm %arg0[@fib_1] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%6, %1, %4) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %7 = struct.readm %6[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %4, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %8 = struct.readm %arg0[@adv_2_2] : <@Main<[]>>, !felt.type<"bn254">
      %9 = struct.readm %6[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@fib_2] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%10, %4, %8) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %11 = struct.readm %10[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %8, %11 : !felt.type<"bn254">, !felt.type<"bn254">
      %12 = struct.readm %arg0[@adv_2_3] : <@Main<[]>>, !felt.type<"bn254">
      %13 = struct.readm %10[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %12, %13 : !felt.type<"bn254">, !felt.type<"bn254">
      %14 = struct.readm %arg0[@fib_3] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%14, %8, %12) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %15 = struct.readm %14[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %12, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %16 = struct.readm %arg0[@adv_2_4] : <@Main<[]>>, !felt.type<"bn254">
      %17 = struct.readm %14[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %16, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %18 = struct.readm %arg0[@fib_4] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%18, %12, %16) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %19 = struct.readm %18[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %16, %19 : !felt.type<"bn254">, !felt.type<"bn254">
      %20 = struct.readm %arg0[@adv_2_5] : <@Main<[]>>, !felt.type<"bn254">
      %21 = struct.readm %18[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %20, %21 : !felt.type<"bn254">, !felt.type<"bn254">
      %22 = struct.readm %arg0[@fib_5] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%22, %16, %20) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %23 = struct.readm %22[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %20, %23 : !felt.type<"bn254">, !felt.type<"bn254">
      %24 = struct.readm %arg0[@adv_2_6] : <@Main<[]>>, !felt.type<"bn254">
      %25 = struct.readm %22[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %24, %25 : !felt.type<"bn254">, !felt.type<"bn254">
      %26 = struct.readm %arg0[@fib_6] : <@Main<[]>>, !struct.type<@fib<[]>>
      function.call @fib::@constrain(%26, %20, %24) : (!struct.type<@fib<[]>>, !felt.type<"bn254">, !felt.type<"bn254">) -> ()
      %27 = struct.readm %26[@out_0] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %24, %27 : !felt.type<"bn254">, !felt.type<"bn254">
      %28 = struct.readm %arg0[@adv_2_7] : <@Main<[]>>, !felt.type<"bn254">
      %29 = struct.readm %26[@out_1] : <@fib<[]>>, !felt.type<"bn254">
      constrain.eq %28, %29 : !felt.type<"bn254">, !felt.type<"bn254">
      %30 = felt.add %0, %1 : !felt.type<"bn254">, !felt.type<"bn254">
      %31 = struct.readm %arg0[@adv_2_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %30, %31 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %1, %arg2 : !felt.type<"bn254">, !felt.type<"bn254">
      %32 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %24, %32 : !felt.type<"bn254">, !felt.type<"bn254">
      %33 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %28, %33 : !felt.type<"bn254">, !felt.type<"bn254">
      function.return
    }
    struct.member @adv_0_0 : !felt.type<"bn254"> 
    struct.member @adv_1_0 : !felt.type<"bn254"> 
    struct.member @fib_0 : !struct.type<@fib<[]>>
    struct.member @adv_2_1 : !felt.type<"bn254">
    struct.member @fib_1 : !struct.type<@fib<[]>>
    struct.member @adv_2_2 : !felt.type<"bn254">
    struct.member @fib_2 : !struct.type<@fib<[]>>
    struct.member @adv_2_3 : !felt.type<"bn254">
    struct.member @fib_3 : !struct.type<@fib<[]>>
    struct.member @adv_2_4 : !felt.type<"bn254">
    struct.member @fib_4 : !struct.type<@fib<[]>>
    struct.member @adv_2_5 : !felt.type<"bn254">
    struct.member @fib_5 : !struct.type<@fib<[]>>
    struct.member @adv_2_6 : !felt.type<"bn254">
    struct.member @fib_6 : !struct.type<@fib<[]>>
    struct.member @adv_2_7 : !felt.type<"bn254">
    struct.member @adv_2_0 : !felt.type<"bn254"> 
  }
}
