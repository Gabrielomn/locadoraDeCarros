/*
						Tema 5: Locadora de Carros

	
	( V )	 Existem carros nacionais e importados
	( V )	 Existem clientes vips e clientes nao vips
	( V )  Clientes podem alugar ate 3 carros
	( ? )  Se um cliente tem duas locacoes no seu nome simultaneamente ele vira um cliente VIP
	( ? )  Apenas clientes vip podem alugar carros importados
	( ? )  As devolucoes em dia e atrasadas devem ser registradas no sistema
	( ? )	 Um cliente deixa de ser vip se apresentar alguma devolucao em atraso
	( V )	Cliente precisa ter nome e telefone para poder fazer a locacao ou reserva de um carro
	( V ) Quando um cliente aluga um carro tanto a locadora quando o cliente detem a informacao.
	( X )	 Deve ser possivel reservar um carro que esteja alugado no momento.
	( V ) Existe um numero limitado de veiculos e esse numero eh menor que o numero de clientes
	( V ) Um veiculo so pode ser alugado por um unico cliente por vez
	( X ) Depois que o carro eh devolvido ele passa por uma limpeza antes de ser alugado novamente.


	
*/

one sig Locadora {
	carros: set Carro,
	devolucoes: set Devolucao
}
sig Reserva {
	solicitante: one ClienteCadastrado,
	reservado: one Carro
}

abstract sig Devolucao{
	carro: one Carro,
	cliente: one ClienteCadastrado
}
sig DevolucaoEmDia extends Devolucao{}
sig DevolucaoAtrasada extends Devolucao{}
abstract sig Carro {}
sig CarroImportado extends Carro{}
sig CarroNacional extends Carro{}

sig Cliente{
	cadastrar: lone Cadastrar
}

abstract sig ClienteCadastrado extends Cliente{
	nome: one Nome,
	telefone: one Telefone,
	alugados: set Carro,
	reservar: one Reservar
}
sig ClienteNaoVip extends ClienteCadastrado{
	alugarNac: one AlugarNac,
}
sig ClienteVip extends ClienteCadastrado{
	alugar: one Alugar 
}

sig Nome {}
sig Telefone {}
sig Alugar {}
sig AlugarNac{}
one sig Cadastrar{}
sig Reservar{}


fact {
	--Todos os carros estao ligados a locadora
	all c:Carro | one c.~carros

	--Cada cliente so pode ter 3 carros alugados
	all a:ClienteCadastrado | #(a.alugados) <= 3
	
	--Cada cliente tem um nome unico
	all n:Nome | one n.~nome

	--Carro so pode ser alugado por um cliente ou nenhum
	all c:Carro | lone c.~alugados

	--Numero de carros eh menor que o numero de Clientes
	(#(Locadora.carros)) < (#ClienteCadastrado)

	/*nao tenho ctz se isso ta funcionando como deveria, mas eh para garantir que todos os carros importados
	so sao alugados por clientes vip.*/
	all c:Carro | (ehImportado[c] and estaAlugado[c]) implies ehVip[c.~alugados]

	/*Nao sei se da pra fazer esse negocio de cliente se tornar vip, mas por enquanto isso garante que qualquer um que
	tenha dois ou mais carros alugados eh vip*/
	all c:ClienteCadastrado | #(c.alugados) >= 2 implies ehVip[c]

	--Apenas clientes nao cadastrados podem se cadastrar, e clientes ja cadastrados nao podem se cadastrar
	all c:Cliente | (ehCadastrado[c]) implies (#(c.cadastrar) = 0)
	all c:Cliente | (naoEhCadastrado[c]) implies (#c.cadastrar = 1)

	--A ideia aqui eh que se ele ja esta reservado, entao significa que ele esta alugado no momento
	all c:Carro | some c.~reservado implies estaAlugado[c]

	--Dessa forma se o cliente apresenta uma devolucao atrasada, ele nao eh mais Vip
	all d:DevolucaoAtrasada | !ehVip[d.cliente]

	all c:ClienteCadastrado | (#c.~solicitante != 0 and !ehVip[c]) implies naoEhReservaDeImportado[c.~solicitante]

}

pred naoEhReservaDeImportado[reserva: Reserva]{
	#(reserva.reservado & CarroImportado) = 0
}

pred naoEhCadastrado[cliente: Cliente]{
	!ehCadastrado[cliente]
}

pred ehCadastrado [cliente : Cliente]{
	#(cliente & ClienteCadastrado) = 1
}

pred ehVip[cliente : ClienteCadastrado]{

	#(cliente & ClienteVip) = 1

}

pred estaAlugado[carro : Carro]{
	#(carro.~alugados) >= 1
}

pred ehImportado[carro : Carro]{

	#(carro & CarroImportado) = 1

}


pred show[]{}
run show for 9
