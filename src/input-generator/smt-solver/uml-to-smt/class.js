const SmtMethod = require('./method.js');

class SmtClass {
	constructor(classObject) {
		this.name = classObject.name;
		this.smtCommands = Object.keys(classObject.methods).map((m) => {
			const method = classObject.methods[m];
			const smtMethod = new SmtMethod(method);
			const commands = smtMethod.getCommands().join('\n');

			return {
				name: method.name,
				commands: commands
			};
		});
	}
}

module.exports = SmtClass;
