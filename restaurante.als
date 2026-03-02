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

fact {
    // -=-=-=-=-=- Fatos gerais para Combos -=-=-=-=-=-

    -- Garante que o Combo tem no máximo uma sobremesa.
    all c: Combo | lone s: Sobremesa | contem_prato[c, s]

    -- Assegura que o Combo possui pelo menos um prato principal.
    all c: Combo | some p: Principal | contem_prato[c, p]

    -- Restringe que combos com os mesmos pratos são os mesmos combos.
    all c1, c2: Combo | c1.pratos = c2.pratos iff c1 = c2


    // -=-=-=-=-=- Fatos para Combos Comuns -=-=-=-=-=-

    -- Garante que os combos comuns não terão todos os tipos de pratos (características dos combos especiais).
    all c: Comum | no (c.pratos & Entrada) or no (c.pratos & Sobremesa)


    // -=-=-=-=-=- Fatos para Combos Especiais -=-=-=-=-=-

    -- Combos especiais devem ter pelo menos uma entrada e exatamente uma sobremesa (combina com a restrição geral).
    all c: Especial | (some e: Entrada | contem_prato[c, e]) and (one s: Sobremesa | contem_prato[c, s])


    // -=-=-=-=-=- Fatos para Pratos -=-=-=-=-=-

    -- Pratos não podem ser incompatíveis com si próprios.
    all p1, p2: Prato | incompativeis[p1, p2] implies p1 != p2

    -- Garante que a relação de incompatibilidade é bidirecional.
    all p1, p2: Prato | incompativeis[p1, p2] iff incompativeis[p2, p1]

    -- Não permite que pratos incompatíveis estejam no mesmo combo.
    all p1, p2: Prato | all c: Combo | (incompativeis[p1, p2] and contem_prato[c, p1]) implies not contem_prato[c, p2]
}

pred contem_prato[c: Combo, p: Prato] {
    p in c.pratos
}

pred incompativeis[x: Prato, y: Prato] {
    x in y.incompativeis
}

run exemplo {} for 3

assert voce_nao_eh_especial {
    all c:Comum | (no e:Entrada | contem_prato[c, e]) or (no s:Sobremesa | contem_prato[c, s])
}

assert prato_daora {
    no p: Prato | p.incompativeis = (Prato - p)
}

assert especial_merda {
    no e:Especial | #e.pratos < 3
}

check especial_merda for 10
