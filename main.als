module main

one sig Condominio {
	portao: one Portao,
	moradores: some Morador,
	garagem: one Garagem
}

one sig Portao {
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

fun GetCondominioMorador[m:Morador]: one Condominio {
	moradores.m
}

fun GetGaragemVisitado[v:Visitante]: one Garagem {
	GetCondominioMorador[v.visita].garagem
}

pred Fatos {
	all p:Portao | #portao.p = 1
	all p:Portao | p.cancelaEntrada != p.cancelaSaida
	all p:Portao | p.semaforoEntrada != p.semaforoSaida
	all p1:Portao | all p2:Portao | !(p1 = p2) => (!(p1.cancelaEntrada = p2.cancelaEntrada) 
		and !(p1.cancelaSaida = p2.cancelaSaida) and !(p1.cancelaEntrada = p2.cancelaSaida)
		and !(p1.cancelaSaida = p2.cancelaEntrada) and !(p1.semaforoEntrada = p2.semaforoEntrada) 
		and !(p1.semaforoSaida = p2.semaforoSaida) and !(p1.semaforoEntrada = p2.semaforoSaida)
		and !(p1.semaforoSaida = p2.semaforoEntrada))
	
	all m:Morador | #moradores.m = 1
    all m:Morador | #proprietario.m <= 2
	all m:MoradorDependente | GetCondominioMorador[m] = GetCondominioMorador[m.depende]

	all c:Cancela | c in Portao.cancelaEntrada or c in Portao.cancelaSaida
	all s:Semaforo | s in Portao.semaforoEntrada or s in Portao.semaforoSaida
    
	all v:Visitante | #proprietario.v = 1
	all v:Visitante | proprietario.v in Garagem.vagasVisitantes
	all v:Visitante | proprietario.v in GetGaragemVisitado[v].vagasVisitantes

    all a:Autorizacao | a.veiculo.proprietario in Condominio.moradores

	all v:Veiculo | v.proprietario in Condominio.moradores => #veiculo.v = 1
	all v:Veiculo | v in Garagem.vagasMoradores => v.proprietario in  Condominio.moradores
	all v:Veiculo | v in Garagem.vagasVisitantes => !(v.proprietario in  Condominio.moradores)

	all g:Garagem | #garagem.g = 1
	all g1:Garagem | all g2:Garagem | !(g1 = g2) => #(g1.vagasMoradores & g2.vagasMoradores) = 0
	all g1:Garagem | all g2:Garagem | !(g1 = g2) => #(g1.vagasVisitantes & g2.vagasVisitantes) = 0
}

-- ASSERTS
assert TodoCondominioTemApenasUmPortao{
	all c: Condominio | one c.portao 
}
check TodoCondominioTemApenasUmPortao for 30

assert TodoCondominioTemApenasUmaGaragem{
	all c: Condominio | one c.garagem 
}
check TodoCondominioTemApenasUmaGaragem  for 30

assert TodoCondominioTemPeloMenosUmMorador{
	all c: Condominio | some c.moradores
}
check TodoCondominioTemPeloMenosUmMorador  for 30

assert Nome{
	
}



pred show[]{}
run Fatos for 30
