module main

sig Condominio {
	portao: one Portao,
	moradores: some Morador,
	garagem: one Garagem
}

sig Portao {
	cancelas: set Cancela
} {
	#cancelas = 2
}

sig Cancela {

}

sig Veiculo {

}

sig Morador {
	veiculos: set Veiculo
} {
	#veiculos <= 2
}

sig Garagem {

}

pred Fatos {
	all p:Portao | #portao.p = 1
	all v:Veiculo | #veiculos.v = 1
	all m:Morador | #moradores.m = 1
	all g:Garagem | #garagem.g = 1
	all c:Cancela | #cancelas.c = 1
}

run Fatos for 5
