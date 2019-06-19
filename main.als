module main

one sig Condominio {
	portao: one Portao,
	moradores: some Morador,
	garagem: one Garagem
}

sig Portao {
	cancelas: set Cancela
} {
	#cancelas = 2
}

sig Cancela {}

sig Veiculo {}

abstract sig Morador {
	veiculos: set Veiculo
} {
	#veiculos <= 2
}

sig MoradorTitular extends Morador {}

sig MoradorDependente extends Morador {}

sig Autorizacao {
	proprietario: one Morador,
	veiculo: one Veiculo
}

sig Garagem {}

abstract sig Semaforo {} 

sig SemaforoEntrada extends Semaforo {}

sig SemaforoSaida extends Semaforo {}

fun GetProprietarioVeiculo[v:Veiculo]: one Morador {
	veiculos.v
} 

pred Fatos {
	all v:Veiculo | #veiculos.v = 1
	all v:Veiculo | #veiculo.v = 1
	
	
	all p:Portao | #portao.p = 1
	all m:Morador | #moradores.m = 1
	all g:Garagem | #garagem.g = 1
	all c:Cancela | #cancelas.c = 1
	
	all a:Autorizacao | a.proprietario = GetProprietarioVeiculo[a.veiculo]  
}

pred show[]{}

run Fatos for 5
