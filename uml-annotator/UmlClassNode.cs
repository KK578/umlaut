using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;

namespace UmlAnnotator
{
	public class UmlClassNode
	{
		XmlNode umlClass;
		private Dictionary<string, UmlMethodNode> methods;
		private Dictionary<string, XmlNode> variables;

		// TODO: Hacky exposing dictionary directly.
		// Should only allow access to Keys or the Values.
		public Dictionary<string, UmlMethodNode> Methods
		{
			get { return methods; }
		}
		public Dictionary<string, XmlNode> Variables
		{
			get { return variables; }
		}

		public UmlClassNode(XmlNode umlClass)
		{
			this.umlClass = umlClass;

			ParseClass();
		}

		private void ParseClass()
		{
			XmlNodeList children = umlClass.ChildNodes;

			foreach (XmlNode child in children)
			{
				if (child.Name == "ownedOperationsInternal")
				{
					ParseMethods(child.ChildNodes);
				}
				else if (child.Name == "ownedAttributesInternal")
				{
					ParseVariables(child.ChildNodes);
				}
			}

			PrintDebug();
		}

		private void ParseMethods(XmlNodeList methods)
		{
			this.methods = new Dictionary<string, UmlMethodNode>();

			foreach (XmlNode node in methods)
			{
				UmlMethodNode method = new UmlMethodNode(node);
				string methodName = method.Name;

				this.methods.Add(methodName, method);
			}
		}

		private void ParseVariables(XmlNodeList variables)
		{
			this.variables = new Dictionary<string, XmlNode>();

			foreach (XmlNode variable in variables)
			{
				string variableName = variable.Attributes.GetNamedItem("name").Value;
				this.variables.Add(variableName, variable);
			}
		}

		public void UpdateNodes()
		{
			foreach (UmlMethodNode node in methods.Values)
			{
				node.UpdateNodes();
			}
		}

		private void PrintDebug()
		{
			foreach (KeyValuePair<string, XmlNode> a in variables)
			{
				Console.WriteLine("Variable: " + a.Key);
			}

			foreach (KeyValuePair<string, UmlMethodNode> a in methods)
			{
				Console.WriteLine("Method: " + a.Key);
			}
		}
	}
}
