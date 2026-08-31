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
      %felt_const_0 = felt.const  0 <"bn254">
      %felt_const_1000 = felt.const  1000 <"bn254">
      %0 = struct.readm %arg0[@adv_0_0] : <@Main<[]>>, !felt.type<"bn254">
      %1 = felt.neg %0 : !felt.type<"bn254">
      %2 = struct.readm %arg0[@adv_0_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %1, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %3 = felt.mul %0, %2 : !felt.type<"bn254">, !felt.type<"bn254">
      %4 = struct.readm %arg0[@adv_1_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %3, %4 : !felt.type<"bn254">, !felt.type<"bn254">
      %5 = struct.readm %arg0[@adv_0_2] : <@Main<[]>>, !felt.type<"bn254">
      %6 = felt.neg %5 : !felt.type<"bn254">
      %7 = struct.readm %arg0[@adv_0_3] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %6, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %8 = felt.mul %5, %7 : !felt.type<"bn254">, !felt.type<"bn254">
      %9 = struct.readm %arg0[@adv_1_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %8, %9 : !felt.type<"bn254">, !felt.type<"bn254">
      %10 = struct.readm %arg0[@adv_0_4] : <@Main<[]>>, !felt.type<"bn254">
      %11 = felt.neg %10 : !felt.type<"bn254">
      %12 = struct.readm %arg0[@adv_0_5] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %11, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %13 = felt.mul %10, %12 : !felt.type<"bn254">, !felt.type<"bn254">
      %14 = struct.readm %arg0[@adv_1_4] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %13, %14 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %0, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %5, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      constrain.eq %10, %arg1 : !felt.type<"bn254">, !felt.type<"bn254">
      %15 = struct.readm %arg0[@out_0] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %4, %15 : !felt.type<"bn254">, !felt.type<"bn254">
      %16 = struct.readm %arg0[@out_1] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %9, %16 : !felt.type<"bn254">, !felt.type<"bn254">
      %17 = struct.readm %arg0[@out_2] : <@Main<[]>>, !felt.type<"bn254">
      constrain.eq %14, %17 : !felt.type<"bn254">, !felt.type<"bn254">
      %18 = bool.cmp lt(%0, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t18_0 = bool.not %18 : i1
      %t18_1 = cast.tofelt %t18_0 : i1, !felt.type<"bn254">
      constrain.eq %t18_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
      %19 = bool.cmp ge(%2, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t19_0 = bool.not %19 : i1
      %t19_1 = cast.tofelt %t19_0 : i1, !felt.type<"bn254">
      constrain.eq %t19_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
      %20 = bool.cmp lt(%5, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t20_0 = bool.not %20 : i1
      %t20_1 = cast.tofelt %t20_0 : i1, !felt.type<"bn254">
      constrain.eq %t20_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
      %21 = bool.cmp ge(%7, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t21_0 = bool.not %21 : i1
      %t21_1 = cast.tofelt %t21_0 : i1, !felt.type<"bn254">
      constrain.eq %t21_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
      %22 = bool.cmp lt(%10, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t22_0 = bool.not %22 : i1
      %t22_1 = cast.tofelt %t22_0 : i1, !felt.type<"bn254">
      constrain.eq %t22_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
      %23 = bool.cmp ge(%12, %felt_const_1000) : !felt.type<"bn254">, !felt.type<"bn254">
      
      %t23_0 = bool.not %23 : i1
      %t23_1 = cast.tofelt %t23_0 : i1, !felt.type<"bn254">
      constrain.eq %t23_1, %felt_const_0 : !felt.type<"bn254">, !felt.type<"bn254">
      
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
  }
}
