const SmtClasses = {
	Assertion: require('../classes/Assertion.js'),
	BooleanExpression: require('../classes/BooleanExpression.js'),
	DeclareConst: require('../classes/DeclareConst.js'),
	DeclareFunction: require('../classes/DeclareFunction.js'),
	Echo: require('../classes/Echo.js'),
	FunctionCall: require('../classes/FunctionCall.js'),
	Model: require('../classes/Model.js'),
	StackModifier: require('../classes/StackModifier.js')
};

function declareConst(argumentObj) {
	const n = argumentObj.name;
	const t = argumentObj.type;

	return new SmtClasses.DeclareConst(n, t);
}

function declareFunction(methodObj) {
	const name = methodObj.name;
	const returnType = methodObj.returnType.type;
	const args = methodObj.arguments.map((a) => {
		return a.type;
	});

	return new SmtClasses.DeclareFunction(name, returnType, args);
}

function booleanExpression(conditionObj) {
	const comparison = conditionObj.comparison;
	const args = conditionObj.arguments.map((a) => {
		if ((typeof a) === 'string' || a instanceof SmtClasses.FunctionCall) {
			return a;
		}
		else {
			return booleanExpression(a);
		}
	});

	const expression = new SmtClasses.BooleanExpression(comparison, args);
	expression.setInverted(conditionObj.inverted);

	return expression;
}

function functionCall(methodObj) {
	const name = methodObj.name;
	const args = methodObj.arguments.map((a) => {
		return a.name;
	});

	return new SmtClasses.FunctionCall(name, args);
}

function echo(output) {
	return new SmtClasses.Echo(output);
}

function assertion(condition) {
	if (condition instanceof SmtClasses.BooleanExpression) {
		return new SmtClasses.Assertion(condition);
	}
	else {
		return new SmtClasses.Assertion(booleanExpression(condition));
	}
}

function getValues(values) {
	return new SmtClasses.Model(values);
}

function stackPop() {
	return new SmtClasses.StackModifier('pop');
}

function stackPush() {
	return new SmtClasses.StackModifier('push');
}

module.exports = {
	assertion,
	booleanExpression,
	declareConst,
	declareFunction,
	echo,
	functionCall,
	getValues,
	stackPop,
	stackPush
};
