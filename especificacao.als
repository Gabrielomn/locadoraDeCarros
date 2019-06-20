/*
						Tema 5: Locadora de Carros

	
	( V )	 Existem carros nacionais e importados
	( V )	 Existem clientes vips e clientes nao vips
	( V )  Clientes podem alugar ate 3 carros
	( X )  Se um cliente tem duas locacoes no seu nome simultaneamente ele vira um cliente VIP
	( ? )  Apenas clientes vip podem alugar carros importados
	( X )  As devolucoes em dia e atrasadas devem ser registradas no sistema
	( X )	 Um cliente deixa de ser vip se apresentar alguma devolucao em atraso
	( V )	Cliente precisa ter nome e telefone para poder fazer a locacao ou reserva de um carro
	( V ) Quando um cliente aluga um carro tanto a locadora quando o cliente detem a informacao.
	( X )	 Deve ser possivel reservar um carro que esteja alugado no momento.
	( X ) Existe um numero limitado de veiculos e esse numero eh menor que o numero de clientes
	( X ) Um veiculo so pode ser alugado por um unico cliente por vez
	( X ) Depois que o carro eh devolvido ele passa por uma limpeza antes de ser alugado novamente.


	
*/

one sig Locadora {
	carros: set Carro
}

abstract sig Carro {}
sig CarroImportado extends Carro{}
sig CarroNacional extends Carro{}

abstract sig Cliente{
	nome: one Nome,
	telefone: one Telefone,
	alugados: set Carro
}
sig ClienteNaoVip extends Cliente{
	alugarNac: one AlugarNac,
}
sig ClienteVip extends Cliente{
	alugar: one Alugar 
}

sig Nome {}
sig Telefone {}
sig Alugar {}
sig AlugarNac{}


fact {
	--Todos os carros estao ligados a locadora
	all c:Carro | one c.~carros

	--Cada cliente so pode ter 3 carros alugados
	all a:Cliente | #(a.alugados) <= 3
	
	--Cada cliente tem um nome unico
	all n:Nome | one n.~nome

	--Carro so pode ser alugado por um cliente ou nenhum
	all c:Carro | lone c.~alugados

	--Numero de carros eh menor que o numero de Clientes
	(#(Locadora.carros)) < (#Cliente)

	/*nao tenho ctz se isso ta funcionando como deveria, mas eh para garantir que todos os carros importados
	so sao alugados por clientes vip.*/
	all c:Carro | (ehImportado[c] and estaAlugado[c]) implies ehVip[c.~alugados]

	/*Nao sei se da pra fazer esse negocio de cliente se tornar vip, mas por enquanto isso garante que qualquer um que
	tenha dois ou mais carros alugados eh vip*/
	all c:Cliente | #(c.alugados) >= 2 implies ehVip[c]
}

pred ehVip[cliente : Cliente]{

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
