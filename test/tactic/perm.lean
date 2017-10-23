
import util.meta.tactic

example : list.perm [1,2,3] [3,2,1] :=
by { prove_perm }

example : list.perm [1,2,3,4] [3,2,4,1] :=
by { prove_perm }

example : list.perm [1,2,3,4] [3,1,4] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [1,3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [1,3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }
