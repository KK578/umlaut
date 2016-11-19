function parseVariables(umlClass) {
	const variables = {};

	umlClass.ownedAttributesInternal.map((variable) => {
		const property = variable.property;
		const v = {
			id: property.Id,
			name: property.name,
		};
	});
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

	umlClass.ownedOperationsInternal[0].operation.map((method) => {
		const operation = method;
		const v = {
			id: operation.$.Id,
			name: operation.$.name,
		};

		v.returnType = getReturnType(operation.ownedParameters);
		v.arguments = getArguments(operation.ownedParameters);
		// TODO: Correct this
		v.preconditions = operation.preconditionsInternal;
		v.postconditions = operation.postconditionsInternal;

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
