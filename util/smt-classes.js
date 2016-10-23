const SmtClasses = {
	Assertion: require('../classes/Assertion.js'),
	BooleanExpression: require('../classes/BooleanExpression.js'),
	DeclareConst: require('../classes/DeclareConst.js'),
	DeclareFunction: require('../classes/DeclareFunction.js'),
	FunctionCall: require('../classes/FunctionCall.js'),
	Model: require('../classes/Model.js'),
	StackModifier: require('../classes/StackModifier.js')
};

function DeclareConst(argumentObj) {
	const n = argumentObj.name;
	const t = argumentObj.type;

	return new SmtClasses.DeclareConst(n, t);
}

function DeclareFunction(methodObj) {
	const name = methodObj.name;
	const returnType = methodObj.return.type;
	const args = methodObj.arguments.map((a) => {
		return a.type;
	});

	return new SmtClasses.DeclareFunction(name, returnType, args);
}

function BooleanExpression(conditionObj) {
	const comparison = conditionObj.comparison;
	const args = conditionObj.arguments.map((a) => {
		if ((typeof a) === 'string' || a instanceof SmtClasses.FunctionCall) {
			return a;
		}
		else {
			return BooleanExpression(a);
		}
	});

	const expression = new SmtClasses.BooleanExpression(comparison, args);
	expression.setInverted(conditionObj.inverted);

	return expression;
}

function FunctionCall(methodObj) {
	const name = methodObj.name;
	const args = methodObj.arguments.map((a) => {
		return a.name;
	});

	return new SmtClasses.FunctionCall(name, args);
}

function Assertion(condition) {
	if (condition instanceof SmtClasses.BooleanExpression) {
		return new SmtClasses.Assertion(condition);
	}
	else {
		return new SmtClasses.Assertion(BooleanExpression(condition));
	}
}

function GetValues(values) {
	return new SmtClasses.Model(values);
}

function StackPop() {
	return new SmtClasses.StackModifier('pop');
}

function StackPush() {
	return new SmtClasses.StackModifier('push');
}

module.exports = {
	Assertion,
	BooleanExpression,
	DeclareConst,
	DeclareFunction,
	FunctionCall,
	GetValues,
	StackPop,
	StackPush
};
