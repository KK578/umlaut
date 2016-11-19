function parseVariables(umlClass) {
	const variables = {};

	umlClass.ownedAttributesInternal[0].property.map((variable) => {
		const property = variable;
		const v = {
			id: property.$.Id,
			name: property.$.name,
		};

		variables[v.name] = v;
	});

	return variables;
}

function parseMethods(umlClass) {
	const methods = {};

	function getReturnType(parameters) {
		for (let i = 0; i < parameters.length; i++) {
			const parameter = parameters[i].operationHasOwnedParameters[0].parameter[0];

			if (parameter.$.direction === 'Return') {
				let name = '';
				let type = '';

				if (parameter.$.name) {
					type = parameter.$.name;
				}
				else if (parameter.type_NamedElement) {
					type = parameter.type_NamedElement[0].primitiveTypeMoniker[0].$.LastKnownName;
				}

				return { type };
			}
		}

		// Did not find a return type, so function has void type.
		return { type: 'Void' };
	}

	function getArguments(parameters) {
		const args = [];

		for (let i = 0; i < parameters.length; i++) {
			const parameter = parameters[i].operationHasOwnedParameters[0].parameter[0];

			if (parameter.$.direction === 'In') {
				let type = '';

				if (parameter.$.name) {
					name = parameter.$.name;
				}

				if (parameter.type_NamedElement) {
					type = parameter.type_NamedElement[0].primitiveTypeMoniker[0].$.LastKnownName;
				}
				else {
					type = 'Object';
				}

				args.push({ name, type });
			}
		}

		return args;
	}

	function getConditions(conditions) {
		const c = {};

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const rawString = constraint.specification[0].literalString[0].$.value;

			c.id = constraint.$.Id;
			// TODO: Add a character to split off of while using Visual Studio's inbuilt
			//  property conditions.
			// TODO: Parse condition string into object splitting into comparison and arguments.
			c.string = rawString;
		}

		return c;
	}

	umlClass.ownedOperationsInternal[0].operation.map((method) => {
		const operation = method;
		const v = {
			id: operation.$.Id,
			name: operation.$.name,
		};

		v.returnType = getReturnType(operation.ownedParameters);
		v.arguments = getArguments(operation.ownedParameters);
		v.preconditions = getConditions(operation.preconditionsInternal);
		v.postconditions = getConditions(operation.postconditionsInternal);

		// TODO: Keep as hashmap of method name?
		methods[v.name] = v;
	});

	return methods;
}

function parseClass(umlClass) {
	const c = {};

	c.id = umlClass.$.Id;
	c.name = umlClass.$.name;

	c.variables = parseVariables(umlClass);
	c.methods = parseMethods(umlClass);

	console.log(JSON.stringify(c, null, 2));

	return c;
}

function parse(uml) {
	uml = uml.modelStoreModel;

	const elements = uml.packagedElements;
	elements.map((element) => {
		element.packageHasNamedElement.map((namedElement) => {
			if (namedElement.class) {
				parseClass(namedElement.class[0]);
			}
		});
	});
}

module.exports = parse;
