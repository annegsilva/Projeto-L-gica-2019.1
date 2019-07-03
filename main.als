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

one sig Garagem {
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

fact Fatos {
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
	all m:Morador | proprietario.m in Garagem.vagasMoradores

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

assert TodoCondominioTemApenasUmaGaragem{
	all c: Condominio | one c.garagem 
}

assert TodoCondominioTemPeloMenosUmMorador{
	all c: Condominio | some c.moradores
}

assert MoradorDependenteTemUmMoradorTitular{
	all md: MoradorDependente | one md.depende
}

assert TodoMoradorTaEmUmCondominio {
	all m:Morador | #moradores.m = 1
}

assert CancelaEntradaDiferenteCancelaSaida{
	all p: Portao | p.cancelaEntrada != p.cancelaSaida
}

assert TodaCancelaTaEmUmPortao {
	all c:Cancela | c in Portao.cancelaEntrada or c in Portao.cancelaSaida
}
assert TodoSemaforoTaEmUmPortao {
	all s:Semaforo | s in Portao.semaforoEntrada or s in Portao.semaforoSaida
}

assert SemaforoEntradaDiferenteSemaforoSaida{
	all p: Portao | p.semaforoEntrada != p.semaforoSaida
}

assert VeiculoTemApenasUmProprietario{
	all v: Veiculo | one v.proprietario
}

assert GaragemSoExisteNoCondominio{
	all g: Garagem | #garagem.g = 1
}

assert VeiculoEhDeVisitanteOuMorador{
	all v: Veiculo | v in Garagem.vagasMoradores => !(v in  Garagem.vagasVisitantes)
}

assert VeiculosDeMoradoresTemAutorizacao {
	all v:Veiculo | v.proprietario in Condominio.moradores => (#veiculo.v = 1)
}

assert VeiculosDeVisitanteNaoTemAutorizacao {
	all v:Veiculo | !(v.proprietario in Condominio.moradores) => (#veiculo.v = 0)
}

assert VeiculoSoEmUmaGaragem {
	all g1:Garagem | all g2:Garagem | !(g1 = g2) => #(g1.vagasMoradores & g2.vagasMoradores) = 0
	all g1:Garagem | all g2:Garagem | !(g1 = g2) => #(g1.vagasVisitantes & g2.vagasVisitantes) = 0
}

assert VeiculoNaoEhVisitanteEDeMorador {
	all g1:Garagem | all g2:Garagem | !(g1 = g2) => #(g1.vagasMoradores & g2.vagasVisitantes) = 0
}

check TodoSemaforoTaEmUmPortao for 30
assert MoradorTemAteDoisVeiculos{
	all m: Morador | #proprietario.m <= 2
}

assert VisitanteTemApenasUmCarro{
	all v: Visitante | #proprietario.v= 1
}


check MoradorTemAteDoisVeiculos for 30
run show{}
