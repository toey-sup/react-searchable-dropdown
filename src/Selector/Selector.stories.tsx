import { useState } from 'react';
import { storiesOf } from "@storybook/react";
import Selector, { Props, Choice } from "./Selector";
import { words } from '../../.storybook/const';

const choices: Choice[] = words.map((word) => ({ label: word, id: word }));

const defaultProps: Props = {
  label: '',
  popUpKey: 'Selector-key',
  choiceSections: [{ choices }],
  name: 'Choice',
  placeholder: 'please select a choice',
  id: 'Selector-id',
  handleSelect: ({ value, name }) => { console.log({ value, name })},
  style: { width: '300px' }
}

storiesOf("Selector", module)
  .add("Normal Selector", () => {
    function Parent({ children }: { children: any }) {
      const [label, setLabel] = useState<string>('');
      return <div>{children(label, setLabel)}</div>;
    }
    return (
      <Parent>
        {(label: string, setLabel: (value: string) => void) => (
          <Selector 
            {...defaultProps}
            label={label}
            handleSelect={({ value }) => { setLabel(value.label); }}
          />
        )}
      </Parent>
    );
  })
  .add("Selector With Section Prefix", () => {
    function Parent({ children }: { children: any }) {
      const [label, setLabel] = useState<string>('');
      return <div>{children(label, setLabel)}</div>;
    }
    return (
      <Parent>
        {(label: string, setLabel: (value: string) => void) => (
          <Selector 
            {...defaultProps}
            label={label}
            handleSelect={({ value }) => { setLabel(value.label); }}
            choiceSections={[{ sectionName: 'Special Choice', sectionPrefix: 'Special', choices: [{ label: 'Special One'}, { label: 'Special Two'}, { label: 'Special Three'}, { label: 'Special Four'}]}, { sectionName: 'Normal Choice', choices: choices, sectionPrefix: 'Normal' }] }
          />
        )}
      </Parent>
    );
  })
  .add("Selector With Used Choices", () => {
    function Parent({ children }: { children: any }) {
      const [label, setLabel] = useState<string>('');
      return <div>{children(label, setLabel)}</div>;
    }
    return (
      <Parent>
        {(label: string, setLabel: (value: string) => void) => (
          <Selector 
            {...defaultProps}
            label={label}
            handleSelect={({ value }) => { setLabel(value.label); }}
            choiceSections={[{ choices: words.map((word, index) => ({ label: word, id: word, used: index < 10 })) }]}
          />
        )}
      </Parent>
    );
  })

