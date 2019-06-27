module main

one sig Condominio {
	portao: one Portao,
	moradores: some Morador,
	garagem: one Garagem
}

sig Portao {
	cancelaEntrada: one Cancela,
	cancelaSaida: one Cancela,
	semaforoEntrada: one Semaforo,
	semaforoSaida: one Semaforo
}

sig Cancela {}

abstract sig Pessoa {}

abstract sig Morador extends Pessoa {}

sig MoradorTitular extends Morador {}

sig MoradorDependente extends Morador {
	depende: one MoradorTitular
}

sig Visitante extends Pessoa {
	visita: one Morador
}

sig Veiculo {
    proprietario: one Pessoa
}

sig Autorizacao {
	veiculo: one Veiculo
}

sig Garagem {
	vagasMoradores: set Veiculo,
	vagasVisitantes: set Veiculo
}

sig Semaforo {} 

pred Fatos {
	all p:Portao | #portao.p = 1
	all p:Portao | p.cancelaEntrada != p.cancelaSaida
	all p:Portao | p.semaforoEntrada != p.semaforoSaida
	
	all g:Garagem | #garagem.g = 1

	all m:Morador | #moradores.m = 1
    all m:Morador | #proprietario.m <= 2

	all c:Cancela | c = Portao.cancelaEntrada or c = Portao.cancelaSaida
	all s:Semaforo | s = Portao.semaforoEntrada or s = Portao.semaforoSaida
    
	all v:Visitante | #proprietario.v = 1
	all v:Visitante | proprietario.v in Garagem.vagasVisitantes

    all a:Autorizacao | a.veiculo.proprietario in Condominio.moradores

	all v:Veiculo | v.proprietario in Condominio.moradores => #veiculo.v = 1
	all v:Veiculo | v in Garagem.vagasMoradores => v.proprietario in  Condominio.moradores
	all v:Veiculo | v in Garagem.vagasVisitantes => !(v.proprietario in  Condominio.moradores)
}

pred show[]{}
run Fatos for 10
