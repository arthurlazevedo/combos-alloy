// -=-=-=-=-=- Assinaturas -=-=-=-=-=-

abstract sig Combo {
    pratos: some Prato
}

some sig Comum extends Combo {}
some sig Especial extends Combo {}

abstract sig Prato {
    incompativeis: set Prato
}

some sig Entrada extends Prato {}
some sig Principal extends Prato {}
some sig Sobremesa extends Prato {}

// -=-=-=-=-=- Fatos -=-=-=-=-=-

fact Combos {
    -- Garante que o Combo tem no máximo uma sobremesa.
    all c: Combo | lone s: Sobremesa | contem_prato[c, s]

    -- Assegura que o Combo possui pelo menos um prato principal.
    all c: Combo | some p: Principal | contem_prato[c, p]

    -- Restringe que combos com os mesmos pratos são os mesmos combos.
    all disj c1, c2: Combo | c1.pratos = c2.pratos implies c1 = c2
}

fact CombosComuns {
    -- Garante que os combos comuns não terão todos os tipos de pratos (características dos combos especiais).
    all c: Comum | no (c.pratos & Entrada) or no (c.pratos & Sobremesa)
}

fact CombosEspeciais {
    -- Combos especiais devem ter pelo menos uma entrada e exatamente uma sobremesa (combina com a restrição geral).
    all c: Especial | (some e: Entrada | contem_prato[c, e]) and (one s: Sobremesa | contem_prato[c, s])
}

fact Pratos {
    -- Pratos não podem ser incompatíveis com si próprios.
    all p1, p2: Prato | incompativeis[p1, p2] implies p1 != p2

    -- Garante que a relação de incompatibilidade é bidirecional.
    all disj p1, p2: Prato | incompativeis[p1, p2] iff incompativeis[p2, p1]

    -- Não permite que pratos incompatíveis estejam no mesmo combo.
    all disj p1, p2: Prato, c: Combo | (incompativeis[p1, p2] and contem_prato[c, p1]) implies not contem_prato[c, p2]
}

// -=-=-=-=-=- Predicados -=-=-=-=-=-

pred contem_prato[c: Combo, p: Prato] {
    p in c.pratos
}

pred incompativeis[x: Prato, y: Prato] {
    x in y.incompativeis
}

// -=-=-=-=-=- Asserts -=-=-=-=-=-

-- assert falso, deve falhar
assert prato_nao_tem_mais_de_um_incompativel {
    all p: Prato | #p.incompativeis < 2
}

-- assert falso, deve falhar
assert prato_sempre_tem_incompativel {
    no p: Prato | #p.incompativeis = 0
}

assert prato_compativel_com_si_proprio {
    all p: Prato | not incompativeis[p, p]
}

assert prato_incompativel_bidirecional {
    all p1, p2: Prato | incompativeis[p1, p2] iff incompativeis[p2, p1]
}

assert pratos_incompativeis_separados {
    all c: Combo | all disj p1, p2: c.pratos | not incompativeis[p1, p2]
}

assert algum_dos_pratos_eh_diferente {
    all disj c1, c2: Combo | c1.pratos != c2.pratos
}

assert comum_tem_pratos_necessarios {
    all c: Comum | some (c.pratos & Principal) and lone (c.pratos & Sobremesa)
}

assert combo_tem_max_uma_sobremesa {
    all c: Combo | lone (Sobremesa & c.pratos)
}

assert especial_tem_todos_pratos {
    all e: Especial | #e.pratos >= 3
        and some (e.pratos & Entrada)
        and some (e.pratos & Principal)
        and some (e.pratos & Sobremesa)
}

assert comum_nao_eh_especial {
    all c: Comum | no (c.pratos & Entrada)
        or no (c.pratos & Principal)
        or no (c.pratos & Sobremesa)
}

// -=-=-=-=-=- Executaveis -=-=-=-=-=-

check prato_nao_tem_mais_de_um_incompativel for 5 -- deve achar um contraexemplo
check prato_sempre_tem_incompativel for 5 -- deve achar um contraexemplo


check prato_compativel_com_si_proprio for 5
check prato_incompativel_bidirecional for 5
check pratos_incompativeis_separados for 5
check algum_dos_pratos_eh_diferente for 5
check comum_tem_pratos_necessarios for 5
check combo_tem_max_uma_sobremesa for 5
check especial_tem_todos_pratos for 5
check comum_nao_eh_especial for 5
run exemplo {} for 5
