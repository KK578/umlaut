const chai = require('chai');
const expect = chai.expect;

const testee = require('../../src/uml-parser/util/classes.js');
let TestClass;

describe('UML Parser Classes', () => {
	describe('AnnotatedUmlClass', () => {
		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a name', () => {
			const obj = new TestClass('foo');

			expect(obj.id).to.be.a('string').and.not.equal('');
			expect(obj.name).to.equal('foo');
		});

		describe('Class Variable Modifiers', () => {
			let obj;

			describe('#addVariable', () => {
				beforeEach(() => {
					obj = new TestClass();
				});

				it('should error on empty input', () => {
					expect(obj.addVariable).to.throw(Error);
				});

				it('should take a name', () => {
					obj.addVariable('a');

					expect(obj.variables).to.include.keys('a');
					expect(obj.variables['a']).to.include({ type: 'object' });
				});

				it('should take a name and type', () => {
					obj.addVariable('a', 'int');

					expect(obj.variables).to.include.keys('a');
					expect(obj.variables['a']).to.include({ type: 'Integer' });
				});

				it('should error if variable name already exists', () => {
					obj.addVariable('a', 'int');

					expect(obj.variables).to.include.keys('a');
					expect(obj.variables['a']).to.include({ type: 'Integer' });

					expect(obj.addVariable.bind(obj, 'a', 'int')).to.throw(Error);
				});
			});

			describe('#addInvariant', () => {
				beforeEach(() => {
					obj = new TestClass();
				});

				it('should error on empty', () => {
					expect(obj.addInvariant).to.throw(Error);
				});

				it('should add a new invariant, as a string, to the class', () => {
					const invariantsLength = obj.invariants.length;

					obj.addInvariant('(> a 0)');

					expect(obj.invariants.length).to.equal(invariantsLength + 1);
				});

				it('should error if invariant string is not bracketed');
				it('should error if invariant string does not specify the comparator');
				it('should add a new invariant, as an object, to the class');
				it('should error if invariant object does not specify the comparator');
				it('should error if invariant object does not specify at least 1 item in arguments');
			});
		});

		describe('Class Method Modifiers', () => {
			let obj;

			describe('#addMethod', () => {
				beforeEach(() => {
					obj = new TestClass();
				});

				it('should error on empty input', () => {
					expect(obj.addMethod).to.throw(Error);
				});

				it('should take a name', () => {
					const methodsLength = obj.methods.length;

					obj.addMethod('foo');

					expect(obj.methods.length).to.equal(methodsLength + 1);
					expect(obj.methods).to.include.keys('foo');
				});

				it('should take a name and type', () => {
					obj.addMethod('foo', 'Integer');

					expect(obj.methods).to.include.keys('foo');
					expect(obj.methods['foo']).to.include({ type: 'Integer' });
				});

				it('should take a name and type and list of arguments', () => {
					obj.addMethod('foo', 'Integer', [{ a: { type: 'Integer' } }]);

					expect(obj.methods).to.include.keys('foo');
					expect(obj.methods['foo']).to.include({ type: 'Integer' });
					expect(obj.methods['foo']).to.include({ a: { type: 'Integer' } });
				});

				it('should error if list of arguments is not an array', () => {
					expect(obj.addMethod.bind(obj, 'foo', 'Integer', 'a')).to.throw(Error);
				});

				it('should error if method name already exists', () => {
					obj.addMethod('foo', 'Integer');

					expect(obj.addMethod.bind(obj, 'foo', 'Integer')).to.throw(Error);
				});
			});

			describe('#setMethodType', () => {
				it('should error on empty');
				it('should error with just a name');
				it('should change the named method\'s return type');
				it('should error if method does not exist');
			});

			describe('#addMethodArgument', () => {
				it('should error on empty');
				it('should error with just a name');
				it('should add a new argument, as a string, to the named method');
				it('should error if argument string does not specify a type');
				it('should add a new argument, as an object, to the named method');
				it('should error if added argument does not have a name');
				it('should error if added argument does not have a type');
				it('should error if method does not exist');
				it('should error if argument name already exists in that method');
			});

			describe('#addMethodPrecondition', () => {
				it('should error on empty');
				it('should error with just a name');
				it('should add a new precondition, as a string, to the named method');
				it('should error if precondition string is not bracketed');
				it('should error if precondition string does not specify the comparator');
				it('should add a new precondition, as an object, to the named method');
				it('should error if precondition object does not specify the comparator');
				it('should error if precondition object does not specify at least 1 item in arguments');
				it('should error if method does not exist');
			});

			describe('#addMethodPostcondition', () => {
				it('should error on empty');
				it('should error with just a name');
				it('should add a new precondition, as a string, to the named method');
				it('should error if precondition string is not bracketed');
				it('should error if precondition string does not specify the comparator');
				it('should add a new precondition, as an object, to the named method');
				it('should error if precondition object does not specify the comparator');
				it('should error if precondition object does not specify at least 1 item in arguments');
				it('should error if method does not exist');
			});
		});
	});
});
