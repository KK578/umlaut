const promises = require('../../../util/promises.js');
const cfgParser = require('./condition-cfg-parser.js');

const classes = require('../../util/classes.js');
const AnnotatedUmlClass = classes.AnnotatedUmlClass;

function getTypeFromNode(parameter) {
	let type = '';

	if (parameter.type_NamedElement) {
		const namedElement = parameter.type_NamedElement[0];

		if (namedElement.primitiveTypeMoniker) {
			type = namedElement.primitiveTypeMoniker[0].$.LastKnownName;
		}
		else if (namedElement.undefinedTypeMoniker) {
			type = namedElement.undefinedTypeMoniker[0].$.LastKnownName;
		}
		else if (namedElement.referencedTypeMoniker) {
			type = namedElement.referencedTypeMoniker[0].$.LastKnownName;
		}
		else {
			throw new Error('Could not find type.');
		}
	}
	else {
		type = 'Object';
	}

	return type;
}

function parseVariables(umlClass) {
	const variables = [];

	// Iterate through list of attributes.
	if (umlClass.ownedAttributesInternal !== undefined) {
		const properties = umlClass.ownedAttributesInternal[0].property;

		properties.forEach((property) => {
			const v = {
				name: property.$.name
			};

			v.visibility = property.$.visibility ? property.$.visibility : 'Public';
			v.type = getTypeFromNode(property);

			variables.push(v);
		});
	}

	return variables;
}

function parseMethods(umlClass) {
	const methods = [];

	// Helper function to get function return type.
	function getReturnType(parameters) {
		let type = 'Void';

		if (parameters) {
			// Must iterate through all and find first that is a return property.
			const parameterList = parameters[0].operationHasOwnedParameters;
			// Filter to find the first parameter that is the return type.
			const parameter = parameterList.map((parameterListing) => {
				// <parameter> node exists under each <operationHasOwnedParameters> node.
				// Return the value contained within the <parameter> node.
				return parameterListing.parameter[0];
			}).filter((parameter) => {
				return parameter.$.direction === 'Return';
			})[0];

			if (parameter) {
				// TODO: Will the system support Python's multiple object return?'
				type = getTypeFromNode(parameter);
			}
		}

		return type;
	}

	// Helper function to get function arguments to array of { name, type }.
	function getArguments(parameters) {
		const args = [];

		if (parameters) {
			const parameterList = parameters[0].operationHasOwnedParameters;

			parameterList.map((parameterListing) => {
				// <parameter> node exists under each <operationHasOwnedParameters> node.
				// Return the value contained within the <parameter> node.
				return parameterListing.parameter[0];
			}).filter((parameter) => {
				return parameter.$.direction === 'In';
			}).forEach((parameter) => {
				args.push({
					name: parameter.$.name,
					type: getTypeFromNode(parameter)
				});
			});
		}

		return args;
	}

	// Helper function to take a condition from XML format to standardised format.
	function getConditions(conditions) {
		let c = [];

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const conditionString = constraint.specification[0].literalString[0].$.value;

			if (!(conditionString === '' || conditionString === '()')) {
				c = cfgParser(conditionString);
			}
		}

		return c;
	}

	// Iterate through all methods.
	if (umlClass.ownedOperationsInternal !== undefined) {
		const operations = umlClass.ownedOperationsInternal[0].operation;

		operations.forEach((operation) => {
			// Generic method properties
			const v = {
				name: operation.$.name
			};

			v.visibility = operation.$.visibility ? operation.$.visibility : 'Public';

			// Types
			v.type = getReturnType(operation.ownedParameters);
			v.arguments = getArguments(operation.ownedParameters);

			// Conditions
			v.preconditions = getConditions(operation.preconditionsInternal);
			v.optionalPreconditions = getConditions(operation.bodyConditionsInternal);
			v.postconditions = getConditions(operation.postconditionsInternal);

			// TODO: Keep method list as a hashmap of method name?
			methods.push(v);
		});
	}

	return methods;
}

function parseClass(umlClass) {
	const c = new AnnotatedUmlClass(umlClass.$.name);

	// Parse information for class variables and methods.
	parseVariables(umlClass).forEach((variable) => {
		c.addVariable(variable);
	});
	parseMethods(umlClass).forEach((method) => {
		c.addMethod(method);

		method.preconditions.forEach((condition) => {
			c.methods[method.name].addPrecondition(condition);
		});

		method.optionalPreconditions.forEach((condition) => {
			c.methods[method.name].addOptionalPrecondition(condition);
		});

		method.postconditions.forEach((condition) => {
			c.methods[method.name].addPostcondition(condition);
		});
	});

	return c;
}

function parse(data) {
	return promises.xmlParseString(data).then((uml) => {
		// Enter root item.
		if (uml.modelStoreModel) {
			uml = uml.modelStoreModel;
		}
		else if (uml.logicalClassDesignerModel) {
			uml = uml.logicalClassDesignerModel;
		}

		const classes = {};
		const elements = uml.packagedElements[0];

		function parsePackages(packages) {
			packages.filter((package) => {
				return package.class !== undefined;
			}).map((namedElement) => {
				return namedElement.class[0];
			}).forEach((classElement) => {
				const c = parseClass(classElement);

				classes[c.name] = c;
			});
		}

		if (elements.packageHasNamedElement) {
			parsePackages(elements.packageHasNamedElement);
		}

		if (elements.logicalClassDesignerModelHasTypes) {
			parsePackages(elements.logicalClassDesignerModelHasTypes);
		}

		return classes;
	});
}

module.exports = parse;
