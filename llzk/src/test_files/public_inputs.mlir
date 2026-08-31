module attributes {llzk.lang = "halo2", llzk.main = !struct.type<@Main<[]>>} {
  struct.def @Main {
    function.def @compute(%arg0: !felt.type {llzk.pub = #llzk.pub}, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}) -> !struct.type<@Main<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@Main<[]>>
      function.return %self : !struct.type<@Main<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@Main<[]>>, %arg1: !felt.type {llzk.pub = #llzk.pub}, %arg2: !felt.type {llzk.pub = #llzk.pub}, %arg3: !felt.type {llzk.pub = #llzk.pub}) attributes {function.allow_constraint, function.allow_non_native_field_ops, function.allow_verif_ops} {
      function.return
    }
  }
}
