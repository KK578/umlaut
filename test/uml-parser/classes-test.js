const REGEX_UUID = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

const testee = require('../../uml-parser/util/classes.js');
let TestClass;

describe('UML Parser Classes', function () {
	describe('AnnotatedUmlClass', function () {
		before(function () {
			TestClass = testee.AnnotatedUmlClass;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on empty object', function () {
			expect(() => {
				new TestClass({});
			}).to.throw(Error);
		});

		it('should take a name', function () {
			const obj = new TestClass('foo');

			expect(obj.id).to.be.a('string').and.match(REGEX_UUID);
			expect(obj.name).to.equal('foo');
		});

		it('should define data structures after initialisation', function () {
			const obj = new TestClass('foo');

			expect(obj.variables).to.be.an('object');
			expect(obj.methods).to.be.an('object');
			expect(obj.invariants).to.be.instanceOf(Array);
		});

		describe('#addVariable', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({ name: 'foo' });
			});

			it('should error on empty input', function () {
				expect(obj.addVariable).to.throw(Error);
			});

			it('should error on empty object', function () {
				expect(obj.addVariable.bind(obj, {})).to.throw(Error);
			});

			it('should take a name, as a string', function () {
				obj.addVariable('a');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.have.keys('name', 'id', 'type', 'visibility');
				expect(obj.variables['a'].name).to.equal('a');
				expect(obj.variables['a'].id).to.be.a('string').and.match(REGEX_UUID);
				expect(obj.variables['a'].type).to.equal('Object');
				expect(obj.variables['a'].visibility).to.equal('Public');
			});

			it('should take a name, as an object', function () {
				obj.addVariable({ name: 'a' });

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.have.all.keys('name', 'id', 'type', 'visibility');
				expect(obj.variables['a'].name).to.equal('a');
				expect(obj.variables['a'].id).to.be.a('string').and.match(REGEX_UUID);
				expect(obj.variables['a'].type).to.equal('Object');
				expect(obj.variables['a'].visibility).to.equal('Public');
			});

			it('should take a name and type, as an object', function () {
				obj.addVariable({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.have.keys('name', 'id', 'type', 'visibility');
				expect(obj.variables['a'].name).to.equal('a');
				expect(obj.variables['a'].id).to.be.a('string').and.match(REGEX_UUID);
				expect(obj.variables['a'].type).to.equal('Integer');
				expect(obj.variables['a'].visibility).to.equal('Public');
			});

			it('should take a name, type and visibility, as an object', function () {
				obj.addVariable({
					name: 'a',
					type: 'Integer',
					visibility: 'Private'
				});

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.have.keys('name', 'id', 'type', 'visibility');
				expect(obj.variables['a'].name).to.equal('a');
				expect(obj.variables['a'].id).to.be.a('string').and.match(REGEX_UUID);
				expect(obj.variables['a'].type).to.equal('Integer');
				expect(obj.variables['a'].visibility).to.equal('Private');
			});

			it('should error if variable name already exists', function () {
				obj.addVariable('a');

				expect(obj.variables).to.include.keys('a');

				expect(obj.addVariable.bind(obj, 'a')).to.throw(Error);
			});
		});

		describe('#addMethod', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({ name: 'foo' });
			});

			it('should error on empty input', function () {
				expect(obj.addMethod).to.throw(Error);
			});

			it('should error on empty object', function () {
				expect(obj.addMethod.bind(obj, {})).to.throw(Error);
			});

			it('should error on string input', function () {
				expect(obj.addMethod.bind(obj, 'foo')).to.throw(Error);
			});

			it('should error on just a name, as an object', function () {
				expect(obj.addMethod.bind(obj, { name: 'foo' })).to.throw(Error);
			});

			it('should take a name and type, as an object', function () {
				expect(obj.methods).to.not.include.key('foo');

				obj.addMethod({
					name: 'foo',
					type: 'Integer'
				});

				expect(obj.methods).to.include.key('foo');
			});

			it('should take a name, type and visibility, as an object', function () {
				expect(obj.methods).to.not.include.key('foo');

				obj.addMethod({
					name: 'foo',
					type: 'Integer',
					visibility: 'Private'
				});

				expect(obj.methods).to.include.key('foo');
			});

			it('should take a name, type and array of arguments, as an object', function () {
				expect(obj.methods).to.not.include.key('foo');

				obj.addMethod({
					name: 'foo',
					type: 'Integer',
					arguments: [
						{
							name: 'a',
							type: 'Integer'
						}
					]
				});

				expect(obj.methods).to.include.key('foo');
			});

			it('should error if list of arguments is not an Array', function () {
				expect(obj.addMethod.bind(obj, {
					name: 'foo',
					type: 'Integer',
					arguments: {
						name: 'a',
						type: 'Integer'
					}
				})).to.throw(Error);
			});

			it('should error if method name already exists', function () {
				obj.addMethod({
					name: 'foo',
					type: 'Integer'
				});

				// Validate method is added.
				expect(obj.methods).to.include.keys('foo');

				// Test adding method again.
				expect(obj.addMethod.bind(obj, {
					name: 'foo',
					type: 'Integer'
				})).to.throw(Error);
			});
		});

		describe('#addInvariant', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({ name: 'foo' });
			});

			it('should error on empty', function () {
				expect(obj.addInvariant).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addInvariant.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new invariant', function () {
				const invariantLength = obj.invariants.length;

				obj.addInvariant({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.invariants.length).to.equal(invariantLength + 1);
			});

			it('should error if invariant object does not specify the comparison', function () {
				expect(obj.addInvariant.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if invariant object does not specify at least 1 item in arguments', function () {
				expect(obj.addInvariant.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});

			it('should generate a unique ID for the condition');
		});
	});

	describe('UmlAnnotatedMethod', function () {
		before(function () {
			TestClass = testee.AnnotatedUmlMethod;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on empty object', function () {
			expect(() => {
				new TestClass({});
			}).to.throw(Error);
		});

		it('should error on a string input', function () {
			expect(() => {
				new TestClass('foo');
			}).to.throw(Error);
		});

		it('should error with just a name, as an object', function () {
			expect(() => {
				new TestClass({ name: 'foo' });
			}).to.throw(Error);
		});

		it('should take a name and type', function () {
			const obj = new TestClass({
				name: 'foo',
				type: 'Integer'
			});

			expect(obj).to.include.keys('id', 'type', 'visibility', 'arguments');
			expect(obj.id).to.be.a('string').and.match(REGEX_UUID);
			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
			expect(obj.visibility).to.equal('Public');
			expect(obj.arguments).to.be.an('object');
		});

		it('should take a name, type and visibility, as an object', function () {
			const obj = new TestClass({
				name: 'foo',
				type: 'Integer',
				visibility: 'Private'
			});

			expect(obj).to.include.keys('id', 'type', 'visibility', 'arguments');
			expect(obj.id).to.be.a('string').and.match(REGEX_UUID);
			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
			expect(obj.visibility).to.equal('Private');
			expect(obj.arguments).to.be.an('object');
		});

		it('should take a name, type and array of arguments, as an object', function () {
			const obj = new TestClass({
				name: 'foo',
				type: 'Integer',
				arguments: [
					{
						name: 'a',
						type: 'Integer'
					}
				]
			});

			expect(obj).to.include.keys('id', 'type', 'visibility', 'arguments');
			expect(obj.id).to.be.a('string').and.match(REGEX_UUID);
			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
			expect(obj.visibility).to.equal('Public');
			expect(obj.arguments).to.be.an('object').and.include({ a: 'Integer' });
		});

		it('should error if list of arguments is not an array', function () {
			expect(() => {
				new TestClass({
					name: 'foo',
					type: 'Integer',
					arguments: {
						name: 'a',
						type: 'Integer'
					}
				});
			}).to.throw(Error);
		});

		it('should define data structures after initialisation', function () {
			const obj = new TestClass({
				name: 'foo',
				type: 'Integer'
			});

			expect(obj.preconditions).to.be.instanceOf(Array);
			expect(obj.postconditions).to.be.instanceOf(Array);
		});

		describe('#setType', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					name: 'foo',
					type: 'Integer'
				});
			});

			it('should error on empty', function () {
				expect(obj.setType).to.throw(Error);
			});

			it('should take a type name', function () {
				expect(obj.type).to.not.equal('String');

				obj.setType('String');

				expect(obj.type).to.equal('String');
			});
		});

		describe('#addArgument', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					name: 'foo',
					type: 'Integer'
				});
			});

			it('should error on empty', function () {
				expect(obj.addArgument).to.throw(Error);
			});

			it('should error on empty object', function () {
				expect(obj.addArgument.bind(obj, {})).to.throw(Error);
			});

			it('should add a new argument, as an object', function () {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.arguments).to.include({ a: 'Integer' });
			});

			it('should error if argument object does not have a name', function () {
				expect(obj.addArgument.bind(obj, { type: 'Integer' })).to.throw(Error);
			});

			it('should error if argument object does not have a type', function () {
				expect(obj.addArgument.bind(obj, { name: 'a' })).to.throw(Error);
			});

			it('should error if argument name already exists in that method', function () {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				// Validate the argument now exists.
				expect(obj.arguments).to.include({ a: 'Integer' });

				expect(obj.addArgument.bind(obj, {
					name: 'a',
					type: 'Integer'
				})).to.throw(Error);
			});
		});

		describe('#addPrecondition', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					name: 'foo',
					type: 'Integer'
				});
			});

			it('should error on empty', function () {
				expect(obj.addPrecondition).to.throw(Error);
			});

			it('should error on empty object', function () {
				expect(obj.addPrecondition.bind(obj, {})).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addPrecondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new precondition', function () {
				const preconditionsLength = obj.preconditions.length;

				obj.addPrecondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.preconditions.length).to.equal(preconditionsLength + 1);
			});

			it('should generate a unique ID for the condition', function () {
				obj.addPrecondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.preconditions[0].id).to.be.a('string').and.match(REGEX_UUID);
			});

			it('should error if precondition object does not specify the comparison', function () {
				expect(obj.addPrecondition.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if precondition object does not specify at least 1 item in arguments', function () {
				expect(obj.addPrecondition.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});
		});

		describe('#addPostcondition', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					name: 'foo',
					type: 'Integer'
				});
			});

			it('should error on empty', function () {
				expect(obj.addPostcondition).to.throw(Error);
			});

			it('should error on empty object', function () {
				expect(obj.addPostcondition.bind(obj, {})).to.throw(Error);
			});

			it('should error if argument is not an object', function () {
				expect(obj.addPostcondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new postcondition', function () {
				const postconditionsLength = obj.postconditions.length;

				obj.addPostcondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.postconditions.length).to.equal(postconditionsLength + 1);
			});

			it('should generate a unique ID for the condition', function () {
				obj.addPostcondition({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});

				expect(obj.postconditions[0].id).to.be.a('string').and.match(REGEX_UUID);
			});

			it('should error if postcondition object does not specify the comparison', function () {
				expect(obj.addPostcondition.bind(obj, {
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if postcondition object does not specify at least 1 item in arguments', function () {
				expect(obj.addPostcondition.bind(obj, {
					comparison: 'LessThan',
					arguments: []
				})).to.throw(Error);
			});
		});
	});

	describe('OclCondition', function () {
		before(function () {
			TestClass = testee.OclCondition;
		});

		it('should error on empty', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on empty object', function () {
			expect(() => {
				new TestClass({});
			}).to.throw(Error);
		});

		it('should error if condition is not an object', function () {
			expect(() => {
				new TestClass('(> a b)');
			}).to.throw(Error);
		});

		it('should take a condition object', function () {
			const obj = new TestClass({
				comparison: 'LessThan',
				arguments: [
					'a',
					'b'
				]
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.arguments).to.include('a').and.include('b');
			expect(obj.isInverted).to.not.be.ok;
		});

		it('should error if condition does not have a comparison', function () {
			expect(() => {
				new TestClass({
					comparison: undefined,
					arguments: [
						'a',
						'b'
					]
				});
			}).to.throw(Error);
		});

		it('should error if condition is not an Array', function () {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					arguments: 'a, b'
				});
			}).to.throw(Error);
		});

		it('should error if condition does not have at least one argument', function () {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					arguments: []
				});
			}).to.throw(Error);
		});

		it('should set isInverted value in object', function () {
			const obj = new TestClass({
				comparison: 'LessThan',
				arguments: [
					'a',
					'b'
				],
				isInverted: true
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.arguments).to.include('a').and.include('b');
			expect(obj.isInverted).to.be.ok;
		});

		describe('#setInverted', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty input', function () {
				expect(obj.setInverted).to.throw(Error);
			});

			it('should error if value is not a boolean', function () {
				expect(obj.setInverted.bind(obj, 'true')).to.throw(Error);
			});

			it('should set isInverted flag to value', function () {
				// Validate change occurs due to method call.
				expect(obj.isInverted).to.be.not.ok;

				obj.setInverted(true);

				expect(obj.isInverted).to.be.ok;
			});
		});

		describe('#setException', function () {
			let obj;

			beforeEach(function () {
				obj = new TestClass({
					comparison: 'LessThan',
					arguments: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty', function () {
				expect(obj.setException).to.throw(Error);
			});

			it('should take type name for an Exception', function () {
				expect(obj.exception).to.be.undefined;

				obj.setException('NullException');

				expect(obj.exception).to.include({ type: 'NullException' });
			});
		});
	});
});
