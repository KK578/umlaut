const Smt = require('../util/classes.js');
const comparisons = require('../../../util/comparisons.js');

const constants = [];

function convertType(type) {
	switch (type) {
		case 'Integer':
			return 'Int';

		case 'Float':
		case 'Double':
			return 'Real';

		default:
			return type;
	}
}

function getConstants() {
	return Object.keys(constants);
}

function declareArguments(args) {
	// For every argument to the function, add a declaration to SMT.
	Object.keys(args).forEach((name) => {
		const type = convertType(args[name]);
		const command = new Smt.DeclareConst(name, type);

		// Note the existence of the argument to the class for get-value calls later.
		if (!constants[name]) {
			constants[name] = true;
		}

		this.commands.push(command);
	});
}

function declareFunction(method) {
	// Declare the function to SMT.
	const type = convertType(method.type);
	const args = Object.keys(method.arguments).map((t) => {
		return convertType(method.arguments[t]);
	});
	const command = new Smt.DeclareFunction(method.name, type, args);

	this.commands.push(command);
}

function allValidConditions(method) {
	// Add a layer to the stack so we can pop later and keep the declarations.
	this.commands.push(new Smt.Echo('[[Valid]]'));
	this.commands.push(new Smt.StackModifier('push'));

	// For each precondition, add it to the stack.
	method.preconditions.forEach((c) => {
		const comparison = comparisons.toSmtSymbol(c.comparison);
		const conditionCommand = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

		this.commands.push(new Smt.Assertion(conditionCommand));
	});

	// Declare a variable for the result
	if (method.type !== 'void') {
		const resultType = convertType(method.type);
		const resultDeclare = new Smt.DeclareConst('result', resultType);

		const functionArgs = Object.keys(method.arguments);
		const functionCall = new Smt.FunctionCall(method.name, functionArgs);
		const resultAssert = new Smt.Assertion(
			new Smt.BooleanExpression('=', ['result', functionCall])
		);

		this.commands.push(resultDeclare);
		this.commands.push(resultAssert);
	}

	// Add postconditions so that the inputs may be more interesting.
	method.postconditions.forEach((c) => {
		const comparison = comparisons.toSmtSymbol(c.comparison);
		const conditionCommand = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

		this.commands.push(new Smt.Assertion(conditionCommand));
	});

	// Check satisfiability and get values of arguments.
	this.commands.push(new Smt.GetValue(getConstants()));
	this.commands.push(new Smt.StackModifier('pop'));
}

function singularInvalidConditions(method) {
	method.preconditions.forEach((a, i) => {
		// For each precondition, add it to the stack.
		this.commands.push(new Smt.Echo(`~~[[${a.id}]]`));
		this.commands.push(new Smt.StackModifier('push'));

		method.preconditions.map((c, j) => {
			const comparison = comparisons.toSmtSymbol(c.comparison);
			const expression = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

			// If it is the one that we are testing,
			//  invert the result and get the values to use as inputs.
			if (i === j) {
				expression.setInverted(!expression.isInverted);
			}

			this.commands.push(new Smt.Assertion(expression));
		});

		this.commands.push(new Smt.GetValue(getConstants()));
		this.commands.push(new Smt.StackModifier('pop'));
	});
}

function optionalConditions(method) {
	if (!Array.isArray(method.optionalPreconditions) ||
		method.optionalPreconditions.length === 0) {
		return;
	}

	// Add a layer to the stack so we can pop later and keep the declarations.
	this.commands.push(new Smt.Echo('[[ValidOptional]]'));
	this.commands.push(new Smt.StackModifier('push'));

	// Optional preconditions are bound under the main preconditions, so they must also be
	//  fulfilled.
	// For each precondition, add it to the stack.
	method.preconditions.forEach((c) => {
		const comparison = comparisons.toSmtSymbol(c.comparison);
		const conditionCommand = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

		this.commands.push(new Smt.Assertion(conditionCommand));
	});

	// Generate input when all optional preconditions are fulfilled.
	this.commands.push(new Smt.StackModifier('push'));

	method.optionalPreconditions.forEach((c) => {
		const comparison = comparisons.toSmtSymbol(c.comparison);
		const expression = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

		this.commands.push(new Smt.Assertion(expression));
		this.commands.push(new Smt.GetValue(getConstants()));
		this.commands.push(new Smt.StackModifier('pop'));
	});

	this.commands.push(new Smt.StackModifier('pop'));

	// Generate inputs when one optional precondition is complemented.
	method.optionalPreconditions.forEach((a, i) => {
		// For each optional precondition, add it to the stack.
		this.commands.push(new Smt.Echo(`~~[[${a.id}]]`));
		this.commands.push(new Smt.StackModifier('push'));

		method.optionalPreconditions.map((c, j) => {
			const comparison = comparisons.toSmtSymbol(c.comparison);
			const expression = new Smt.BooleanExpression(comparison, c.arguments, c.inverted);

			// If it is the one that we are testing,
			//  invert the result and get the values to use as inputs.
			if (i === j) {
				expression.setInverted(!expression.isInverted);
			}

			this.commands.push(new Smt.Assertion(expression));
		});

		this.commands.push(new Smt.GetValue(getConstants()));
		this.commands.push(new Smt.StackModifier('pop'));
	});

	this.commands.push(new Smt.StackModifier('pop'));
}

module.exports = class SmtMethod {
	constructor(method) {
		this.commands = [];

		declareArguments.call(this, method.arguments);
		declareFunction.call(this, method);
		allValidConditions.call(this, method);
		singularInvalidConditions.call(this, method);
		optionalConditions.call(this, method);
	}

	getCommands() {
		return this.commands;
	}
};
